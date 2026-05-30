import Lean

namespace Comparator
namespace Disproof

open Lean

abbrev LevelSubst := Std.HashMap Name Level
abbrev MatchM := ReaderT (Std.HashSet Name) <| StateT LevelSubst <| Except String

def mkNot (p : Expr) : Expr :=
  mkApp (mkConst ``Not) p

partial def preprocessExpr (e : Expr) : Expr :=
  match e.cleanupAnnotations with
  | .app (.app (.app (.const ``Ne lvls) α) lhs) rhs =>
    mkNot <| mkApp (mkApp (mkApp (mkConst ``Eq lvls) (preprocessExpr α)) (preprocessExpr lhs)) (preprocessExpr rhs)
  | .app f a => .app (preprocessExpr f) (preprocessExpr a)
  | .lam n ty body bi => .lam n (preprocessExpr ty) (preprocessExpr body) bi
  | .forallE n ty body bi => .forallE n (preprocessExpr ty) (preprocessExpr body) bi
  | .letE n ty val body nondep => .letE n (preprocessExpr ty) (preprocessExpr val) (preprocessExpr body) nondep
  | .mdata m e => .mdata m (preprocessExpr e)
  | .proj n i e => .proj n i (preprocessExpr e)
  | e => e

partial def substLevel (subst : LevelSubst) (l : Level) : Level :=
  match l with
  | .succ l => .succ (substLevel subst l)
  | .max u v => .max (substLevel subst u) (substLevel subst v)
  | .imax u v => .imax (substLevel subst u) (substLevel subst v)
  | .param n => subst[n]?.getD l
  | l => l

partial def matchLevel (expected actual : Level) : MatchM Unit := do
  let expected := (substLevel (← get) expected).normalize
  let actual := actual.normalize
  go expected actual
where
  go (expected actual : Level) : MatchM Unit := do
    match expected, actual with
    | .zero, .zero => pure ()
    | .succ u, .succ v => matchLevel u v
    | .max u₁ u₂, .max v₁ v₂
    | .imax u₁ u₂, .imax v₁ v₂ =>
      matchLevel u₁ v₁
      matchLevel u₂ v₂
    | .param n, actual =>
      if (← read).contains n then
        match (← get)[n]? with
        | some assigned =>
          if assigned == actual then pure ()
          else throw s!"universe parameter {n} mapped inconsistently: {assigned} vs {actual}"
        | none => modify (·.insert n actual)
      else if expected == actual then
        pure ()
      else
        throw s!"universe mismatch: expected {expected}, got {actual}"
    | _, _ =>
      if expected == actual then pure ()
      else throw s!"universe mismatch: expected {expected}, got {actual}"

partial def matchLevels : List Level → List Level → MatchM Unit
  | [], [] => pure ()
  | u :: us, v :: vs => matchLevel u v *> matchLevels us vs
  | _, _ => throw "different number of universe levels"

def notArg? (e : Expr) : Option Expr :=
  match e.cleanupAnnotations with
  | .app (.const n _) p => if n == ``Not then some p else none
  | _ => none

def existsBody? (e : Expr) : Option (Expr × Expr × Expr) :=
  match e.cleanupAnnotations with
  | .app (.app (.const n _) ty) (.lam _ lamTy body _) =>
    if n == ``Exists then some (ty, lamTy, body) else none
  | _ => none

mutual
partial def matchExpr (expected actual : Expr) : MatchM Unit := do
  let expected := preprocessExpr expected |>.cleanupAnnotations
  let actual := preprocessExpr actual |>.cleanupAnnotations
  match expected, actual with
  | .bvar i, .bvar j => unless i == j do throw s!"bound variable mismatch: {i} vs {j}"
  | .fvar i, .fvar j => unless i == j do throw "free variable mismatch"
  | .mvar i, .mvar j => unless i == j do throw "metavariable mismatch"
  | .sort u, .sort v => matchLevel u v
  | .const n us, .const m vs =>
    unless n == m do throw s!"constant mismatch: {n} vs {m}"
    matchLevels us vs
  | .app f a, .app g b =>
    matchExpr f g
    matchExpr a b
  | .lam _ ty body _, .lam _ ty' body' _
  | .forallE _ ty body _, .forallE _ ty' body' _ =>
    matchExpr ty ty'
    matchExpr body body'
  | .letE _ ty val body _, .letE _ ty' val' body' _ =>
    matchExpr ty ty'
    matchExpr val val'
    matchExpr body body'
  | .lit v, .lit w => unless v == w do throw "literal mismatch"
  | .proj n i e, .proj m j e' =>
    unless n == m && i == j do throw s!"projection mismatch: {n}.{i} vs {m}.{j}"
    matchExpr e e'
  | _, _ => throw s!"expression mismatch:\nexpected: {expected}\nactual: {actual}"

partial def matchForallsAsExists (challengeType solutionType : Expr) : MatchM Unit := do
  let challengeType := preprocessExpr challengeType |>.cleanupAnnotations
  let solutionType := preprocessExpr solutionType |>.cleanupAnnotations
  match challengeType with
  | .forallE _ ty body _ =>
    let some (existsTy, lamTy, existsBody) := existsBody? solutionType
      | throw s!"expected existential disproof binder, got:\n{solutionType}"
    matchExpr ty existsTy
    matchExpr ty lamTy
    matchForallsAsExists body existsBody
  | conclusion => matchTerminal conclusion solutionType

partial def matchTerminal (challengeConclusion solutionConclusion : Expr) : MatchM Unit := do
  let challengeConclusion := preprocessExpr challengeConclusion |>.cleanupAnnotations
  let solutionConclusion := preprocessExpr solutionConclusion |>.cleanupAnnotations
  match notArg? challengeConclusion with
  | some positive => matchExpr positive solutionConclusion
  | none =>
    match notArg? solutionConclusion with
    | some negated => matchExpr challengeConclusion negated
    | none => throw s!"expected terminal negation, got:\n{solutionConclusion}"
end

def check (challengeLevelParams : List Name) (challengeType solutionType : Expr) : Except String Unit :=
  let allowed := Std.HashSet.ofList challengeLevelParams
  match (matchForallsAsExists challengeType solutionType).run allowed |>.run {} with
  | .ok _ => .ok ()
  | .error e => .error e

end Disproof
end Comparator
