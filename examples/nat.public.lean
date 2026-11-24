/- Natural numbers: recursion, induction, and equality reasoning.
   Lemmas proved earlier can be used inside later proofs (they are inlined
   into the private proof term), but not in public statements. -/

inductive False : Prop where
inductive True : Prop where
  | intro : True
def Not (A : Prop) : Prop := A → False

inductive Eq (A : Type) (a : A) : A → Prop where
  | refl : Eq A a a

inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

def add (m n : Nat) : Nat :=
  Nat.rec.{1} (fun (_ : Nat) => Nat) m (fun (k : Nat) (ih : Nat) => Nat.succ ih) n
def mul (m n : Nat) : Nat :=
  Nat.rec.{1} (fun (_ : Nat) => Nat) Nat.zero (fun (k : Nat) (ih : Nat) => add ih m) n
def pred (n : Nat) : Nat :=
  Nat.rec.{1} (fun (_ : Nat) => Nat) Nat.zero (fun (k : Nat) (ih : Nat) => k) n
def isZero (n : Nat) : Prop :=
  Nat.rec.{1} (fun (_ : Nat) => Prop) True (fun (k : Nat) (ih : Prop) => False) n

def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ one
def three : Nat := Nat.succ two
def six : Nat := Nat.succ (Nat.succ (Nat.succ three))

-- ---- equality ----

theorem eq_symm : ∀ (A : Type) (x y : A), Eq A x y → Eq A y x :=
  sorry

theorem eq_trans : ∀ (A : Type) (x y z : A), Eq A x y → Eq A y z → Eq A x z :=
  sorry

theorem congr : ∀ (A B : Type) (f : A → B) (x y : A), Eq A x y → Eq B (f x) (f y) :=
  sorry

-- ---- computation ----

theorem two_times_three : Eq Nat (mul two three) six := sorry

theorem pred_succ : ∀ (n : Nat), Eq Nat (pred (Nat.succ n)) n :=
  sorry

theorem add_zero : ∀ (n : Nat), Eq Nat (add n Nat.zero) n :=
  sorry

theorem add_succ : ∀ (m n : Nat), Eq Nat (add m (Nat.succ n)) (Nat.succ (add m n)) :=
  sorry

-- ---- constructors are injective and disjoint ----

theorem succ_ne_zero : ∀ (n : Nat), Not (Eq Nat (Nat.succ n) Nat.zero) :=
  sorry

theorem succ_inj : ∀ (m n : Nat), Eq Nat (Nat.succ m) (Nat.succ n) → Eq Nat m n :=
  sorry

-- ---- induction ----

theorem zero_add : ∀ (n : Nat), Eq Nat (add Nat.zero n) n :=
  sorry

theorem succ_add : ∀ (m n : Nat), Eq Nat (add (Nat.succ m) n) (Nat.succ (add m n)) :=
  sorry

theorem add_assoc : ∀ (a b c : Nat), Eq Nat (add (add a b) c) (add a (add b c)) :=
  sorry

theorem add_comm : ∀ (m n : Nat), Eq Nat (add m n) (add n m) :=
  sorry
