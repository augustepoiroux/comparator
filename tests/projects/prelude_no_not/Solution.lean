prelude

noncomputable section
set_option linter.unusedVariables false
set_option genCtorIdx false

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

inductive True : Prop where
  | intro : True

inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

inductive Bool : Type where
  | false : Bool
  | true : Bool

inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

def Nat.add (a b : Nat) : Nat := a
def Nat.sub (a b : Nat) : Nat := a
def Nat.mul (a b : Nat) : Nat := a
def Nat.pow (a b : Nat) : Nat := a
def Nat.gcd (a b : Nat) : Nat := a
def Nat.div (a b : Nat) : Nat := a
def Nat.mod (a b : Nat) : Nat := a
def Nat.beq (a b : Nat) : Bool := Bool.true
def Nat.ble (a b : Nat) : Bool := Bool.true
def Nat.land (a b : Nat) : Nat := a
def Nat.lor (a b : Nat) : Nat := a
def Nat.xor (a b : Nat) : Nat := a
def Nat.shiftLeft (a b : Nat) : Nat := a
def Nat.shiftRight (a b : Nat) : Nat := a

inductive List (α : Type u) : Type u where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

inductive Char : Type where
  | mk (val : Nat) : Char

def Char.ofNat (n : Nat) : Char := Char.mk n

inductive String : Type where
  | mk (data : List Char) : String

def String.ofList (l : List Char) : String := String.mk l

def eagerReduce {α : Sort u} (a : α) : α := a
def optParam (α : Sort u) (default : α) : Sort u := α
def autoParam (α : Sort u) (tactic : Nat) : Sort u := α
def semiOutParam (α : Sort u) : Sort u := α
def outParam (α : Sort u) : Sort u := α

init_quot

axiom sorryAx (α : Sort u) : α

theorem challenge : Eq Nat.zero Nat.zero := Eq.refl Nat.zero
