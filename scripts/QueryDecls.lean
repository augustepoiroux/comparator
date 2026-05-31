import Lean

def main (args : List String) : IO Unit := do
  let mode := args[0]!
  let oleanPath := args[1]!
  let (modData, _) ← Lean.readModuleData oleanPath
  if mode == "find-sorry-theorems" then
    for ci in modData.constants do
      match ci with
      | .thmInfo val =>
        if val.value.getUsedConstants.contains `sorryAx then
          IO.println val.name.toString
      | _ => pure ()
  else if mode == "find-sorry-defs" then
    for ci in modData.constants do
      match ci with
      | .defnInfo val =>
        if val.value.getUsedConstants.contains `sorryAx then
          IO.println val.name.toString
      | .opaqueInfo val =>
        if val.value.getUsedConstants.contains `sorryAx then
          IO.println val.name.toString
      | _ => pure ()
  else if mode == "list-decls" then
    for ci in modData.constants do
      IO.println ci.name.toString
  else
    throw <| .userError s!"Unknown mode: {mode}"
