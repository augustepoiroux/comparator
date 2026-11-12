universe u v w
private abbrev inner : Prop := ∀ (_ : Sort (w + 1)), True
theorem lvl_valid (_ : Type (imax 1 (max u v))) : True := sorry
theorem lvl_invalid (_ : Sort (imax (u + 1) v)) : True := sorry
theorem lvl_order_ab (h1 : inner.{max u v}) (h2 : inner.{max u v}) : True := sorry
theorem lvl_order_ba (h1 : inner.{max u v}) (h2 : inner.{max u v}) : True := sorry
