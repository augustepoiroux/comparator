theorem max_universe_chal.disproof (h : ∀ (α : Type 0) (β : Type 1), ¬(ULift.{max 0 1} Nat = ULift.{max 0 1} Nat)) : False :=
  h PUnit PUnit rfl
