import Lean

namespace Comparator

namespace Disproof

open Lean

def mkAnd (p q : Expr) : Expr :=
  mkApp2 (mkConst ``And) p q

def mkOr (p q : Expr) : Expr :=
  mkApp2 (mkConst ``Or) p q

def mkNot (p : Expr) : Expr :=
  mkApp (mkConst ``Not) p

partial def negateExpr (e : Expr) : Expr :=
  let e := e.cleanupAnnotations
  match e with
  | .app (.app (.const ``And _) p) q =>
    .forallE `_ p (negateExpr q) .default
  | .forallE name ty body binfo =>
    let body' := .lam name ty (negateExpr body) binfo
    mkApp2 (mkConst ``Exists [Level.succ Level.zero]) ty body'
  | .app (.app (.const ``Or _) p) q =>
    mkAnd (negateExpr p) (negateExpr q)
  | .app (.app (.const ``Exists _) _) (.lam name btype body binfo) =>
    .forallE name btype (negateExpr body) binfo
  | .lam name btype body binfo =>
    .lam name btype (negateExpr body) binfo
  | .app (.app (.app (.const ``Ne lvls) α) p) q =>
    .app (.app (.app (.const ``Eq lvls) α) p) q
  | .app (.const ``Not _) p =>
    p
  | _ =>
    mkNot e

mutual

partial def isEquiv (a b : Expr) : Bool :=
  match a, b with
  | .app (.app (.app (.const ``Ne lvls1) α1) p1) q1, .app (.const ``Not _) (.app (.app (.app (.const ``Eq lvls2) α2) p2) q2) =>
    lvls1 == lvls2 && isEquiv α1 α2 && isEquiv p1 p2 && isEquiv q1 q2
  | .app (.const ``Not _) (.app (.app (.app (.const ``Eq lvls1) α1) p1) q1), .app (.app (.app (.const ``Ne lvls2) α2) p2) q2 =>
    lvls1 == lvls2 && isEquiv α1 α2 && isEquiv p1 p2 && isEquiv q1 q2
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .mvar i, .mvar j => i == j
  | .sort l1, .sort l2 => l1 == l2
  | .const n1 l1, .const n2 l2 => n1 == n2 && l1 == l2
  | .app f1 a1, .app f2 a2 => isEquiv f1 f2 && isEquiv a1 a2
  | .lam _ t1 b1 _, .lam _ t2 b2 _ => isEquiv t1 t2 && isEquiv b1 b2
  | .forallE _ t1 b1 _, .forallE _ t2 b2 _ => isEquiv t1 t2 && isEquiv b1 b2
  | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ => isEquiv t1 t2 && isEquiv v1 v2 && isEquiv b1 b2
  | .lit v1, .lit v2 => v1 == v2
  | .mdata _ e1, .mdata _ e2 => isEquiv e1 e2
  | .proj n1 i1 e1, .proj n2 i2 e2 => n1 == n2 && i1 == i2 && isEquiv e1 e2
  | _, _ => false

end

end Disproof
end Comparator
