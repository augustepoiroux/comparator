theorem foo.disproof (h : ∀ (α : Type 0) (β : Type 1), False) : False :=
  h PUnit PUnit.{1}
