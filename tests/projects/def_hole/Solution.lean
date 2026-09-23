def n : Nat := 17
def m : { k : Nat // k = n * 2 } := ⟨34, rfl⟩

theorem foo : n + 17 = 34 := rfl
theorem bar : m.val + 1 = 35 := rfl
