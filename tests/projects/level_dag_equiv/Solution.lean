universe u v w
private abbrev inner : Prop := ∀ (_ : Sort (w + 1)), True
theorem lvl_valid (_ : Sort (max (u + 1) (v + 1))) : True := trivial
theorem lvl_invalid (_ : Sort (max (u + 1) v)) : True := trivial
theorem lvl_order_ab (h1 : inner.{max u v}) (h2 : inner.{imax 1 (max u v)}) : True := trivial
theorem lvl_order_ba (h1 : inner.{imax 1 (max u v)}) (h2 : inner.{max u v}) : True := trivial
