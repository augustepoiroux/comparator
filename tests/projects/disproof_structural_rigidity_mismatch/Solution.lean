/- Proves disproof under a structure target with varying field universe levels. -/
structure MyStruct.{u} where
  A : Type u
  B : Type u

theorem foo.disproof (h : ∀ (s : MyStruct.{1}) (x : s.B), False) : False :=
  h ⟨PUnit.{2}, PUnit.{2}⟩ PUnit.unit.{2}
