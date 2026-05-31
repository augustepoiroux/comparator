import Lean

def main (args : List String) : IO Unit := do
  let mode := args[0]!
  let oleanPath := args[1]!
  let (modData, _) ← Lean.readModuleData oleanPath
  if mode == "find-sorry-theorems" then
    for ci in modData.constants do
      if let .thmInfo val := ci then
        if val.value.getUsedConstants.contains `sorryAx then
          IO.println val.name.toString
  else if mode == "find-sorry-defs" then
    for ci in modData.constants do
      if let .defnInfo val := ci then
        if val.value.getUsedConstants.contains `sorryAx then
          IO.println val.name.toString
  else if mode == "list-decls" then
    for ci in modData.constants do
      IO.println ci.name.toString
  else
    throw <| .userError s!"Unknown query mode: {mode}"
