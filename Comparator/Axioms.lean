/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.Util
import Export.Parse

namespace Comparator

namespace Axioms

structure Context where
  solution : Export.ExportedEnv
  legalAxioms : Std.HashSet Lean.Name

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name

abbrev AxiomsM := ReaderT Context <| StateT State <| Except String

def addWorklist (n : Lean.Name) : AxiomsM Unit := do
  if !(← get).checked.contains n then
    modify fun s => { worklist := s.worklist.push n, checked := s.checked.insert n }

partial def loop : AxiomsM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  let some info := (← read).solution.constMap[target]?
    | throw s!"Constant not found in solution '{target}'"

  runForUsedConsts info validateConst
  loop
where
  validateConst (n : Lean.Name) : AxiomsM Unit := do
    if !(← get).checked.contains n then
      let some info := (← read).solution.constMap[n]?
        | throw s!"Constant not found in solution '{n}'"

      if let .axiomInfo info := info then
        if !(← read).legalAxioms.contains info.name then
          throw s!"Illegal axiom detected: '{n}'"

      addWorklist n

end Axioms

def checkAxioms (solution : Export.ExportedEnv) (theoremTargets : Array Lean.Name)
    (definitionTargets : Array Lean.Name) (legalAxioms : Array Lean.Name)
    (checked : Std.HashSet Lean.Name := {}) : Except String (Std.HashSet Lean.Name) := do
  let mut worklist := #[]
  for target in theoremTargets do
    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"
    let .thmInfo solutionConst := solutionConst
      | throw s!"Solution constant is not a theorem: '{target}'"
    worklist := worklist.push solutionConst.name

  for target in definitionTargets do
    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"
    let .defnInfo solutionConst := solutionConst
      | throw s!"Solution constant is not a definition: '{target}'"
    worklist := worklist.push solutionConst.name

  let legalAxioms := Std.HashSet.ofArray legalAxioms
  let (_, s) ← (do worklist.forM Axioms.addWorklist; Axioms.loop).run
    { solution, legalAxioms } |>.run { worklist := #[], checked }
  return s.checked

end Comparator
