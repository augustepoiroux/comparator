import Lean

def main (args : List String) : IO Unit := do
  let mode := args[0]!
  unless mode == "find-sorry-theorems" || mode == "find-sorry-defs" do
    throw <| .userError s!"Unknown query mode: {mode}"

  let oleanPath : System.FilePath := args[1]!
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

  let mut seen : Std.HashSet Lean.Name := {}
  let mut names : Array Lean.Name := #[]
  for (modData, _) in parts do
    for ci in modData.constants do
      -- A private name is mangled with its defining module (`_private.Challenge.0.foo`), so the
      -- solution module can never declare it. Discovering one guarantees an unsatisfiable target.
      if Lean.isPrivateName ci.name then
        continue
      let value? := match mode, ci with
        | "find-sorry-theorems", .thmInfo v => some v.value
        | "find-sorry-defs", .defnInfo v => some v.value
        | _, _ => none
      if let some v := value? then
        if v.getUsedConstants.contains `sorryAx && !seen.contains ci.name then
          seen := seen.insert ci.name
          names := names.push ci.name
  IO.println <| Lean.Json.compress <| Lean.ToJson.toJson names
