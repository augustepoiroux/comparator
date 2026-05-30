structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

theorem polymorphic_challenge.disproof
    (h : ∀ {α : Type u} (x : α), Nonempty (Equiv α PUnit.{u+1})) : False := by
  have h_equiv_nonempty :=
    h (α := Sum PUnit.{u+1} PUnit.{u+1}) (Sum.inl PUnit.unit)
  cases h_equiv_nonempty with
  | intro h_equiv =>
    have h_inl := h_equiv.left_inv (Sum.inl PUnit.unit)
    have h_inr := h_equiv.left_inv (Sum.inr PUnit.unit)
    have h_contra : Sum.inl PUnit.unit = Sum.inr PUnit.unit := Eq.trans (Eq.symm h_inl) h_inr
    nomatch h_contra
