def hole : Nat := sorry
abbrev MyNat := Nat
private theorem _posSucc (k : Nat) : 0 < k + 1 := Nat.zero_lt_succ k

-- Positive Q1 cases: open aux apps under unrelated hole binders/lets & abbrev domains
theorem base (n : Nat) : (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0 := sorry
theorem ord_a : (∀ n : Nat, (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0) ∧
    ∀ (h : hole = 5), (∀ n : Nat, (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0) ∧ h = h := sorry
theorem ord_b : (∀ (h : hole = 5), (∀ n : Nat, (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0) ∧ h = h) ∧
    (∀ n : Nat, (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0) := sorry
theorem unrelated (h : hole = 5) (n : Nat) : h = h ∧ (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0 := sorry
theorem dead_binder (h : hole = 5) (n : Nat) : (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0 := sorry
theorem masked_middle (h : hole = 5) (_unused : MyNat) (n : Nat) :
    (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0 ∧ h = h := sorry
theorem dead_let : let _x := hole; ∀ n : Nat, (⟨0, _posSucc (n + 1)⟩ : Fin ((n + 1) + 1)).val = 0 := sorry

def P (_ : Nat) : Prop := True
def Hold {p : Prop} (_ : p) : Prop := True
private theorem _pAux (k : Nat) : P k := trivial
theorem abbrev_dom (h : hole = 5) (n : MyNat) : h = h ∧ Hold (_pAux n) := sorry
theorem abbrev_dom_nohole (n : MyNat) : Hold (_pAux n) := sorry

def hH : Nat := 5
private theorem auxH (n : Nat) (_h : n = 5) : True := trivial
theorem tgtH : let x : Nat := hH; ∀ m : Nat, Hold (auxH (m - m + 5) (by omega)) ∨ x = 6 := sorry

-- Soundness exploit attempts against Loop 1 / Loop 2 (all 6 must be REJECTED)
def HoldFalse (_ : True) : Prop := False

def TA : Type := Nat
private theorem auxA (_x : Nat) : True := trivial
theorem tgtA : ∀ (y : TA), HoldFalse (auxA y) := sorry

def TB : Type := Nat
theorem tgtB : ∀ (y : TB), HoldFalse (auxA (Nat.succ y)) := sorry

def hC : Nat := 5
private theorem auxC (n : Nat) (_h : n = 5) : True := trivial
theorem tgtC : let x : Nat := hC; HoldFalse (auxC x (@rfl Nat 5)) ∨ x = 6 := sorry

def hD : Nat := 5
def QD (_ : Nat) : Prop := True
private theorem auxD (_h : QD 5) : True := trivial
theorem tgtD : let x : Nat := hD; ∀ (p : QD x), HoldFalse (auxD p) ∨ x = 6 := sorry

def hF : Nat := 5
private theorem auxF (n : Nat) (_h : n = hF) : True := trivial
theorem tgtF : HoldFalse (auxF 5 (@rfl Nat 5)) ∨ hF = 6 := sorry

def hG : Nat := 5
theorem lemG : hG = 5 := rfl
private theorem auxG (_ : (5 : Nat) = 5) : True := trivial
theorem tgtG : HoldFalse (auxG lemG) ∨ hG = 6 := sorry
