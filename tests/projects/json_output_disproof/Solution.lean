theorem foo.disproof : ¬ (∀ x : Nat, ¬ 1 + 1 = 2) := fun h => h 0 rfl
