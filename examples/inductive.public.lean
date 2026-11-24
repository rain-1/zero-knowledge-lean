/- zkLean example library: inductive types.
   Every argument is explicit, including parameters and motives, and a
   recursor that can eliminate into any universe takes its universe as
   `I.rec.{u}` (`.{0}` for proofs by induction, `.{1}` to compute data). -/

inductive False : Prop where

inductive True : Prop where
  | intro : True

inductive And (A B : Prop) : Prop where
  | intro (a : A) (b : B) : And A B

inductive Or (A B : Prop) : Prop where
  | inl (a : A) : Or A B
  | inr (b : B) : Or A B

def Not (A : Prop) : Prop := A → False

inductive Eq (A : Type) (a : A) : A → Prop where
  | refl : Eq A a a

inductive Bool : Type where
  | false : Bool
  | true : Bool

inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

-- Exists is a Prop with a data field, so it only eliminates into Prop.
inductive Exists (A : Type) (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : Exists A P

def add (m n : Nat) : Nat :=
  Nat.rec.{1} (fun (_ : Nat) => Nat) m (fun (k : Nat) (ih : Nat) => Nat.succ ih) n

def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ one
def four : Nat := Nat.succ (Nat.succ two)

-- computation by ι-reduction
theorem two_plus_two : Eq Nat (add two two) four := sorry

theorem and_swap : ∀ (A B : Prop), And A B → And B A :=
  sorry

theorem or_swap : ∀ (A B : Prop), Or A B → Or B A :=
  sorry

theorem ex_falso : ∀ (A : Prop), False → A :=
  sorry

-- large elimination: true ≠ false
theorem true_ne_false : Not (Eq Bool Bool.true Bool.false) :=
  sorry

-- induction: 0 + n = n (n + 0 = n holds by computation)
theorem zero_add : ∀ (n : Nat), Eq Nat (add Nat.zero n) n :=
  sorry

theorem exists_two : Exists Nat (fun (n : Nat) => Eq Nat (add n n) four) :=
  sorry
