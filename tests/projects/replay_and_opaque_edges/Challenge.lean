-- Consolidated E2E regression test for T2b non-nanoda edge cases:
-- 1) #16138 mutual inductive signature-only dependency (`My1`..`My8` only in `C`'s header)
-- 2) `Quot` pre-replay before parallel theorem task dispatch (`q0`..`q7`)
-- 3) `OpaqueVal.all := []` when mutual block mixes public and private `partial def`s
-- 4) Optional custom `permitted_axioms` present in Challenge and omitted in Solution

axiom optionalAx : True

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

theorem mut_ind : Nonempty A := sorry

mutual
partial def f (n : Nat) : Nat := g n
private partial def g (n : Nat) : Nat := f n
end

theorem mut_opaque : f 0 = f 0 := sorry

theorem q0 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := sorry
theorem q1 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := sorry
theorem q2 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := sorry
theorem q3 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := sorry
theorem q4 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := sorry
theorem q5 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := sorry
theorem q6 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := sorry
theorem q7 : @Quot.lift Nat (fun _ _ => True) Nat (fun _ => 0) (fun _ _ _ => rfl) (@Quot.mk Nat (fun _ _ => True) 5) = 0 := sorry
