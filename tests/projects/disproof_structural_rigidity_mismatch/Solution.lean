/- Proves disproof under a structure target with varying field universe levels. -/
structure MyStruct.{u} where
  A : Type u
  B : Type u

theorem foo.disproof : ∃ (s : MyStruct.{1}), ∃ (h : s.B), ¬ False :=
  ⟨⟨PUnit.{2}, PUnit.{2}⟩, PUnit.unit.{2}, fun h => h⟩
