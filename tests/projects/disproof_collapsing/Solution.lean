/-
  SOLUTION DISPROOF: Collapsed Universe Parameters
  Disproves the target by collapsing parameters u and v to w_1 inside the disproof signature,
  proven using inverse composition under strict standard axioms.
-/
structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

theorem polymorphic_challenge.disproof.{w_1} :
  ∃ (α : Type w_1), ∃ (β : Type w_1), ∃ _x : α, ∃ _y : β, ¬ Nonempty (Equiv α β) :=
  ⟨Sum PUnit.{w_1+1} PUnit.{w_1+1}, PUnit.{w_1+1}, Sum.inl PUnit.unit, PUnit.unit, by
    intro h
    cases h with
    | intro h_equiv =>
      have h_inl := h_equiv.left_inv (Sum.inl PUnit.unit)
      have h_inr := h_equiv.left_inv (Sum.inr PUnit.unit)
      have h_contra : Sum.inl PUnit.unit = Sum.inr PUnit.unit := Eq.trans (Eq.symm h_inl) h_inr
      nomatch h_contra⟩
