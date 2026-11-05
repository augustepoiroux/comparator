-- `T` is a definition hole whose challenge value `Nat` makes `chalAux y` well-typed.
def T : Type := Nat
private theorem chalAux (_x : Nat) : True := trivial
def Hold (_ : True) : Prop := False
theorem tgt : ∀ (y : T), Hold (chalAux y) := sorry
