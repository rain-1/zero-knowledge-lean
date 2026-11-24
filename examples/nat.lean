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
  fun (A : Type) (x y : A) (h : Eq A x y) =>
    Eq.rec.{0} A x (fun (z : A) (_ : Eq A x z) => Eq A z x) (Eq.refl A x) y h

theorem eq_trans : ∀ (A : Type) (x y z : A), Eq A x y → Eq A y z → Eq A x z :=
  fun (A : Type) (x y z : A) (h : Eq A x y) (k : Eq A y z) =>
    Eq.rec.{0} A y (fun (w : A) (_ : Eq A y w) => Eq A x w) h z k

theorem congr : ∀ (A B : Type) (f : A → B) (x y : A), Eq A x y → Eq B (f x) (f y) :=
  fun (A B : Type) (f : A → B) (x y : A) (h : Eq A x y) =>
    Eq.rec.{0} A x (fun (z : A) (_ : Eq A x z) => Eq B (f x) (f z)) (Eq.refl B (f x)) y h

-- ---- computation ----

theorem two_times_three : Eq Nat (mul two three) six := Eq.refl Nat six

theorem pred_succ : ∀ (n : Nat), Eq Nat (pred (Nat.succ n)) n :=
  fun (n : Nat) => Eq.refl Nat n

theorem add_zero : ∀ (n : Nat), Eq Nat (add n Nat.zero) n :=
  fun (n : Nat) => Eq.refl Nat n

theorem add_succ : ∀ (m n : Nat), Eq Nat (add m (Nat.succ n)) (Nat.succ (add m n)) :=
  fun (m n : Nat) => Eq.refl Nat (Nat.succ (add m n))

-- ---- constructors are injective and disjoint ----

theorem succ_ne_zero : ∀ (n : Nat), Not (Eq Nat (Nat.succ n) Nat.zero) :=
  fun (n : Nat) (h : Eq Nat (Nat.succ n) Nat.zero) =>
    Eq.rec.{0} Nat (Nat.succ n) (fun (m : Nat) (_ : Eq Nat (Nat.succ n) m) => Not (isZero m))
      (fun (f : False) => f) Nat.zero h True.intro

theorem succ_inj : ∀ (m n : Nat), Eq Nat (Nat.succ m) (Nat.succ n) → Eq Nat m n :=
  fun (m n : Nat) (h : Eq Nat (Nat.succ m) (Nat.succ n)) =>
    congr Nat Nat pred (Nat.succ m) (Nat.succ n) h

-- ---- induction ----

theorem zero_add : ∀ (n : Nat), Eq Nat (add Nat.zero n) n :=
  fun (n : Nat) =>
    Nat.rec.{0} (fun (k : Nat) => Eq Nat (add Nat.zero k) k)
      (Eq.refl Nat Nat.zero)
      (fun (k : Nat) (ih : Eq Nat (add Nat.zero k) k) =>
        congr Nat Nat Nat.succ (add Nat.zero k) k ih)
      n

theorem succ_add : ∀ (m n : Nat), Eq Nat (add (Nat.succ m) n) (Nat.succ (add m n)) :=
  fun (m n : Nat) =>
    Nat.rec.{0} (fun (k : Nat) => Eq Nat (add (Nat.succ m) k) (Nat.succ (add m k)))
      (Eq.refl Nat (Nat.succ m))
      (fun (k : Nat) (ih : Eq Nat (add (Nat.succ m) k) (Nat.succ (add m k))) =>
        congr Nat Nat Nat.succ (add (Nat.succ m) k) (Nat.succ (add m k)) ih)
      n

theorem add_assoc : ∀ (a b c : Nat), Eq Nat (add (add a b) c) (add a (add b c)) :=
  fun (a b c : Nat) =>
    Nat.rec.{0} (fun (k : Nat) => Eq Nat (add (add a b) k) (add a (add b k)))
      (Eq.refl Nat (add a b))
      (fun (k : Nat) (ih : Eq Nat (add (add a b) k) (add a (add b k))) =>
        congr Nat Nat Nat.succ (add (add a b) k) (add a (add b k)) ih)
      c

theorem add_comm : ∀ (m n : Nat), Eq Nat (add m n) (add n m) :=
  fun (m n : Nat) =>
    Nat.rec.{0} (fun (k : Nat) => Eq Nat (add m k) (add k m))
      (eq_symm Nat (add Nat.zero m) m (zero_add m))
      (fun (k : Nat) (ih : Eq Nat (add m k) (add k m)) =>
        eq_trans Nat (Nat.succ (add m k)) (Nat.succ (add k m)) (add (Nat.succ k) m)
          (congr Nat Nat Nat.succ (add m k) (add k m) ih)
          (eq_symm Nat (add (Nat.succ k) m) (Nat.succ (add k m)) (succ_add k m)))
      n
