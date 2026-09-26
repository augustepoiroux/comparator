import Lean
import Export

open Lean

partial def collectAxiomsCached (env : Environment)
    (cache : IO.Ref (Std.HashMap Name (Array Name))) (c : Name) : IO (Array Name) := do
  if let some axs := (← cache.get)[c]? then return axs
  cache.modify (·.insert c #[])
  let addAx (axs : Array Name) (ax : Name) : Array Name := if axs.contains ax then axs else axs.push ax
  let collectExpr (axs : Array Name) (e : Expr) : IO (Array Name) := do
    let mut axs := axs
    for d in e.getUsedConstants do
      for ax in ← collectAxiomsCached env cache d do axs := addAx axs ax
    return axs
  let mut axs : Array Name := #[]
  match env.find? c with
  | some (.axiomInfo v) => axs ← collectExpr #[c] v.type
  | some (.defnInfo v) | some (.thmInfo v) | some (.opaqueInfo v) =>
    axs ← collectExpr (← collectExpr axs v.type) v.value
  | some (.quotInfo _) | none => pure ()
  | some (.ctorInfo v) => axs ← collectAxiomsCached env cache v.induct
  | some (.recInfo v) =>
    axs ← collectExpr axs v.type
    for indName in v.all do
      for ax in ← collectAxiomsCached env cache indName do axs := addAx axs ax
    for rule in v.rules do axs ← collectExpr axs rule.rhs
  | some (.inductInfo v) =>
    for indName in v.all do cache.modify (·.insert indName #[])
    for indName in v.all do
      if let some (.inductInfo iv) := env.find? indName then
        axs ← collectExpr axs iv.type
        for ctor in iv.ctors do
          if let some (.ctorInfo cv) := env.find? ctor then axs ← collectExpr axs cv.type
    for indName in v.all do cache.modify (·.insert indName axs)
  cache.modify (·.insert c axs)
  return axs

partial def dumpConstantOmitProofs (axiomCache : IO.Ref (Std.HashMap Name (Array Name))) (c : Name) : M Unit := do
  let env := (← read).env
  let some declar := env.find? c | return
  if ((declar.isUnsafe || declar.isPartial) && !(← get).exportUnsafe) || (← get).visitedConstants.contains c then
    return
  let dumpDeps (e : Expr) : M Unit := e.getUsedConstants.forM (dumpConstantOmitProofs axiomCache)
  match declar with
  | .thmInfo val =>
    modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
    dumpDeps val.type
    let exportUnsafe := (← get).exportUnsafe
    let axioms := (← collectAxiomsCached env axiomCache val.name).filter fun ax =>
      match env.find? ax with | some d => (!d.isUnsafe && !d.isPartial) || exportUnsafe | none => false
    axioms.forM (dumpConstantOmitProofs axiomCache)
    let dummyVal := axioms.foldl (fun acc ax => .app acc (.const ax [])) (.bvar 0)
    IO.println <| Json.mkObj [("thm", Json.mkObj [
      ("name", ← dumpName val.name), ("levelParams", ← dumpUparams val.levelParams),
      ("type", ← dumpExpr val.type), ("value", ← dumpExpr dummyVal), ("all", ← dumpNames val.all)
    ])] |>.compress
  | .axiomInfo val =>
    modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
    dumpDeps val.type
    modify fun st => { st with visitedConstants := st.visitedConstants.erase c }
    dumpConstant c
  | .defnInfo val | .opaqueInfo val =>
    modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
    dumpDeps val.type; dumpDeps val.value
    modify fun st => { st with visitedConstants := st.visitedConstants.erase c }
    dumpConstant c
  | .quotInfo _ => dumpConstantOmitProofs axiomCache ``Eq; dumpConstant c
  | .ctorInfo val => dumpConstantOmitProofs axiomCache val.induct
  | .recInfo val => val.all.forM (dumpConstantOmitProofs axiomCache)
  | .inductInfo baseIndVal =>
    let recNames := (← get).recursorMap.get? baseIndVal.name |>.getD {}
    let mut blockNames := recNames.insert c
    for indName in baseIndVal.all do
      blockNames := blockNames.insert indName
      if let some (.inductInfo indVal) := env.find? indName then
        blockNames := indVal.ctors.foldl (·.insert ·) blockNames
    modify fun st => { st with visitedConstants := blockNames.foldl (·.insert ·) st.visitedConstants }
    for indName in baseIndVal.all do
      if let some (.inductInfo indVal) := env.find? indName then
        dumpDeps indVal.type
        for ctor in indVal.ctors do
          if let some (.ctorInfo ctorVal) := env.find? ctor then dumpDeps ctorVal.type
    for recName in recNames do
      if let some (.recInfo recVal) := env.find? recName then
        dumpDeps recVal.type
        for rule in recVal.rules do dumpDeps rule.rhs
    modify fun st => { st with visitedConstants := blockNames.foldl (·.erase ·) st.visitedConstants }
    dumpConstant c

def runExportOmitProofs (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (opts, args) := args.partition (fun s => s.startsWith "--" && s.length ≥ 3)
  let (imports, constants) := args.span (· != "--")
  let imports := imports.toArray.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }
  let env ← importModules imports {}
  let constants := match constants.tail? with
    | some cs => cs.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!
    | none    => env.constants.toList.map Prod.fst |>.filter (!·.isInternal)
  let axiomCache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  M.run env do
    let _ ← initState env opts
    dumpMetadata
    for prim in #[``Nat, ``Char.ofNat, ``String.ofList] do
      if ((← read).env.find? prim).isSome then
        modify (fun st => { st with noMDataExprs := {} })
        dumpConstantOmitProofs axiomCache prim
    for c in constants do
      modify (fun st => { st with noMDataExprs := {} })
      dumpConstantOmitProofs axiomCache c

def main (args : List String) : IO Unit := do
  if args.head? == some "export-omit-proofs" then
    return ← runExportOmitProofs (args.drop 1)
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
