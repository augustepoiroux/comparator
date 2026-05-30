theorem foo.disproof : ∃ (α : Type 0), ∃ (β : Type 1), ¬ False :=
  ⟨PUnit, PUnit.{1}, fun h => h⟩
