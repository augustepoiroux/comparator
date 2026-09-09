inductive MyType where
  | mk (n : Nat) : MyType

@[elab_as_elim]
theorem ind_mk {C : MyType → Prop} (x : MyType) (h : ∀ y, C (.mk y)) : C x := by
  cases x
  exact h _

theorem mk_eq (a b : Nat) : MyType.mk a = MyType.mk b ↔ a = b := by
  constructor
  · intro h; injection h
  · intro h; rw [h]

class MyStruct (α : Type) where
  val : Nat
  refl : ∀ a : α, a = a
  trans : ∀ a b c : α, a = b → b = c → a = c
  antisymm : ∀ a b : α, a = b → b = a → a = b

instance myInst : MyStruct MyType where
  val := 42
  refl a := by
    induction a using ind_mk
    rfl
  trans a b c := by
    induction a using ind_mk
    induction b using ind_mk
    induction c using ind_mk
    intro h1 h2
    exact h1.trans h2
  antisymm a b := by
    induction a using ind_mk
    induction b using ind_mk
    intro h1 _
    exact h1
