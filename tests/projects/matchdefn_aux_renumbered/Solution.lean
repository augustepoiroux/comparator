inductive Wrap (n : Nat) : { y : Nat // y = n } → Prop
| mk (x) : Wrap n x

structure Bundle (n : Nat) : Type where
  a : { y : Nat // y = n }
  b : { _u : Unit // ¬ (n = n) → False }
  w : Wrap n a

theorem lem (n : Nat) : n = n := rfl

def T (n : Nat) : Bundle n :=
  { a := ⟨n, by omega⟩
    b := ⟨(), fun h => id (h (Eq.refl n))⟩
    w := id (Wrap.mk _) }

theorem challenge : (T 0).a.1 = 0 := rfl
