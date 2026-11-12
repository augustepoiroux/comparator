def hole : Nat := 5
abbrev MyNat := Nat
private theorem _mine (n : Nat) : 0 < n + 1 + 1 := by omega
def P (_ : Nat) : Prop := True
def Hold {p : Prop} (_ : p) : Prop := True
private theorem _mine2 (m : MyNat) : P m := trivial

theorem base (n : Nat) : (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0 := rfl
theorem ord_a : (∀ n : Nat, (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0) ∧
    ∀ (h : hole = 5), (∀ n : Nat, (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0) ∧ h = h :=
  ⟨fun _ => rfl, fun _ => ⟨fun _ => rfl, rfl⟩⟩
theorem ord_b : (∀ (h : hole = 5), (∀ n : Nat, (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0) ∧ h = h) ∧
    (∀ n : Nat, (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0) :=
  ⟨fun _ => ⟨fun _ => rfl, rfl⟩, fun _ => rfl⟩
theorem unrelated (h : hole = 5) (n : Nat) : h = h ∧ (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0 := ⟨rfl, rfl⟩
theorem dead_binder (h : hole = 5) (n : Nat) : (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0 := rfl
theorem masked_middle (h : hole = 5) (_unused : MyNat) (n : Nat) :
    (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0 ∧ h = h := ⟨rfl, rfl⟩
theorem dead_let : let _x := hole; ∀ n : Nat, (⟨0, _mine n⟩ : Fin ((n + 1) + 1)).val = 0 := fun _ => rfl
theorem abbrev_dom (h : hole = 5) (n : MyNat) : h = h ∧ Hold (_mine2 n) := ⟨rfl, trivial⟩
theorem abbrev_dom_nohole (n : MyNat) : Hold (_mine2 n) := trivial

def hH : Nat := 6
private theorem sAuxH (_m : Nat) : True := trivial
theorem tgtH : let x : Nat := hH; ∀ m : Nat, Hold (sAuxH m) ∨ x = 6 := fun _ => Or.inr rfl

def HoldFalse (_ : True) : Prop := False
private theorem sAux0 : True := trivial

def TA : Type := Empty
private theorem sAuxA (_x : TA) : True := trivial
theorem tgtA : ∀ (y : TA), HoldFalse (sAuxA y) := fun y => y.elim

def TB : Type := Empty
theorem tgtB : ∀ (y : TB), HoldFalse sAux0 := fun y => y.elim

def hC : Nat := 6
theorem tgtC : let x : Nat := hC; HoldFalse sAux0 ∨ x = 6 := Or.inr rfl

def hD : Nat := 6
def QD (_ : Nat) : Prop := True
theorem tgtD : let x : Nat := hD; ∀ (_p : QD x), HoldFalse sAux0 ∨ x = 6 := fun _ => Or.inr rfl

def hF : Nat := 6
theorem tgtF : HoldFalse sAux0 ∨ hF = 6 := Or.inr rfl

def hG : Nat := 6
theorem tgtG : HoldFalse sAux0 ∨ hG = 6 := Or.inr rfl
