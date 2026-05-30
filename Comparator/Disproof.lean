import Lean

open Lean Meta

namespace Comparator.Disproof

def check (levelParams : List Name) (targetType disproofType : Expr) : IO Bool := do
  initSearchPath (← findSysroot)
  PPContext.runMetaM { env := (← importModules #[{ module := `Init, importAll := true, isExported := false, isMeta := false }] {}) } do
    let targetType := targetType.instantiateLevelParams levelParams (← mkFreshLevelMVars levelParams.length)
    try isDefEq (← mkArrow targetType (mkConst ``False)) disproofType
    catch _ => return false

end Comparator.Disproof
