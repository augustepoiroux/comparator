abbrev My1 := Nat
abbrev My2 := Nat
abbrev My3 := Nat
abbrev My4 := Nat
abbrev My5 := Nat
abbrev My6 := Nat
abbrev My7 := Nat
abbrev My8 := Nat

mutual
inductive A : Type where
  | mk : B → A
inductive B : Type where
  | mk : A → B
  | nil : B
inductive C : My1 → My2 → My3 → My4 → My5 → My6 → My7 → My8 → Type where
  | mk (n : Nat) : A → C n n n n n n n n
end

theorem mut_ind : Nonempty A := ⟨.mk .nil⟩

mutual
partial def f (n : Nat) : Nat := g n
private partial def g (n : Nat) : Nat := f n
end

theorem mut_opaque : f 0 = f 0 := rfl

theorem q0 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := rfl
theorem q1 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := rfl
theorem q2 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := rfl
theorem q3 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := rfl
theorem q4 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := rfl
theorem q5 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := rfl
theorem q6 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := rfl
theorem q7 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := rfl
