structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

theorem polymorphic_challenge.disproof.{w_1}
    (h : ∀ {α : Type w_1} {β : Type w_1} (x : α) (y : β), Nonempty (Equiv α β)) :
    False := by
  have h_equiv_nonempty :=
    h (α := Sum PUnit.{w_1+1} PUnit.{w_1+1}) (β := PUnit.{w_1+1})
      (Sum.inl PUnit.unit) PUnit.unit
  cases h_equiv_nonempty with
  | intro h_equiv =>
    have h_inl := h_equiv.left_inv (Sum.inl PUnit.unit)
    have h_inr := h_equiv.left_inv (Sum.inr PUnit.unit)
    have h_contra : Sum.inl PUnit.unit = Sum.inr PUnit.unit := Eq.trans (Eq.symm h_inl) h_inr
    nomatch h_contra
