import Lean

def main (args : List String) : IO Unit := do
  let oleanPath : System.FilePath := args[0]!
  -- Module-system oleans split their data across three files and the *body* of a `public theorem`
  -- lives in the private part, so reading only the main `.olean` would hide `sorryAx`. Key off
  -- `isModule` (as `Lean.readModuleDataPartsOfMod` does) so a missing part is a hard error.
  let mainPart ← Lean.readModuleData oleanPath
  let parts ←
    if mainPart.1.isModule then
      let serverPath : System.FilePath := oleanPath.toString ++ ".server"
      let privPath : System.FilePath := oleanPath.toString ++ ".private"
      Lean.readModuleDataParts #[oleanPath, serverPath, privPath]
    else
      pure #[mainPart]

  -- All constants defined in this module's parts; prefer a version that carries a value
  -- (the public part of a module-system olean may only hold the signature).
  let mut consts : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for (modData, _) in parts do
    for ci in modData.constants do
      if !consts.contains ci.name || (ci.value? (allowOpaque := true)).isSome then
        consts := consts.insert ci.name ci

  -- `d` belongs to `ci`'s own source declaration: a `where`/`let rec` helper or a compiler
  -- auxiliary of `ci` or of a declaration in its mutual block (`ev._mutual` for `od`).
  let isSubDecl (ci : Lean.ConstantInfo) (d : Lean.Name) : Bool :=
    !Lean.isPrivateName d && ci.all.any fun p => p != d && p.isPrefixOf d
  -- Which used constants pass `sorryAx` on. A definition target is compared by type only, so a
  -- definition only becomes one when its own body, split into compiler-generated definitions
  -- (`foo._f`, `foo._mutual`, ...), has a `sorry`; using another hole or a named helper does not
  -- make it one. A theorem also reaches `sorryAx` through its `where`/`let rec` helpers, and
  -- through private helpers, which can never be targets themselves.
  let propagates (ci : Lean.ConstantInfo) (d : Lean.Name) : Bool :=
    match ci with
    | .thmInfo _ => Lean.isPrivateName d || isSubDecl ci d
    | _ => isSubDecl ci d && d.isInternalDetail && (consts[d]? matches some (.defnInfo _))

  -- A constant reaches `sorryAx` if it uses it directly or uses (type or value) a constant of
  -- this module that reaches it and `propagates`. Computed exactly by a reverse BFS.
  let mut users : Std.HashMap Lean.Name (Array Lean.Name) := {}
  let mut reaches : Std.HashSet Lean.Name := {}
  let mut queue : Array Lean.Name := #[]
  for (n, ci) in consts do
    let used := ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    if used.contains `sorryAx then
      reaches := reaches.insert n
      queue := queue.push n
    for d in used do
      if consts.contains d && propagates ci d then
        users := users.insert d ((users.getD d #[]).push n)
  while !queue.isEmpty do
    let n := queue.back!
    queue := queue.pop
    for u in users.getD n #[] do
      if !reaches.contains u then
        reaches := reaches.insert u
        queue := queue.push u

  -- Reported names, in either mode. A private name is mangled with its defining module
  -- (`_private.Challenge.0.foo`), so the solution module can never declare it: discovering one
  -- guarantees an unsatisfiable target. An internal-detail name (`foo._proof_1`, `foo.match_1`,
  -- `foo.eq_1`, ...) is compiler-generated and numbered per elaboration, so it is skipped when it
  -- is reached through a reported parent: a proper prefix of it that is itself reported. A
  -- theorem is only skipped when its statement is about that parent (equation lemmas); other
  -- internal-detail names (`proof_1`, `_hidden`, `foo.proof_1` for an unrelated `foo`) are
  -- ordinary declarations. Proper prefixes have fewer components, so they are decided first.
  let mut reported : Std.HashSet Lean.Name := {}
  let byLength := consts.toArray.qsort (fun a b => a.1.getNumParts < b.1.getNumParts)
  for (n, ci) in byLength do
    let isThmOrDefn := ci matches .thmInfo _ | .defnInfo _
    if !isThmOrDefn || Lean.isPrivateName n || !reaches.contains n then
      continue
    if n.isInternalDetail then
      let mut p := n.getPrefix
      let mut skip := false
      while !p.isAnonymous && !skip do
        if reported.contains p then
          skip := !(ci matches .thmInfo _) || ci.type.getUsedConstants.any (p.isPrefixOf ·)
        p := p.getPrefix
      if skip then
        continue
    reported := reported.insert n

  let mut seen : Std.HashSet Lean.Name := {}
  let mut thms : Array Lean.Name := #[]
  let mut defs : Array Lean.Name := #[]
  for (modData, _) in parts do
    for ci in modData.constants do
      if reported.contains ci.name && !seen.contains ci.name then
        match ci with
        | .thmInfo _ => seen := seen.insert ci.name; thms := thms.push ci.name
        | .defnInfo _ => seen := seen.insert ci.name; defs := defs.push ci.name
        | _ => pure ()
  IO.println <| Lean.Json.compress <| Lean.ToJson.toJson (thms, defs)
