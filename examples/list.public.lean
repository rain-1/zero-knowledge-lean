/- Polymorphic lists: length, append, map, and their laws. -/

inductive Eq (A : Type) (a : A) : A → Prop where
  | refl : Eq A a a

inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

inductive List (A : Type) : Type where
  | nil : List A
  | cons (x : A) (xs : List A) : List A

def add (m n : Nat) : Nat :=
  Nat.rec.{1} (fun (_ : Nat) => Nat) m (fun (k : Nat) (ih : Nat) => Nat.succ ih) n

def length (A : Type) (l : List A) : Nat :=
  List.rec.{1} A (fun (_ : List A) => Nat) Nat.zero
    (fun (x : A) (xs : List A) (ih : Nat) => Nat.succ ih) l

def append (A : Type) (l r : List A) : List A :=
  List.rec.{1} A (fun (_ : List A) => List A) r
    (fun (x : A) (xs : List A) (ih : List A) => List.cons A x ih) l

def map (A B : Type) (f : A → B) (l : List A) : List B :=
  List.rec.{1} A (fun (_ : List A) => List B) (List.nil B)
    (fun (x : A) (xs : List A) (ih : List B) => List.cons B (f x) ih) l

def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ one
def three : Nat := Nat.succ two
def l12 : List Nat := List.cons Nat one (List.cons Nat two (List.nil Nat))
def l3 : List Nat := List.cons Nat three (List.nil Nat)

-- ---- computation ----

theorem append_example : Eq (List Nat) (append Nat l12 l3)
    (List.cons Nat one (List.cons Nat two (List.cons Nat three (List.nil Nat)))) :=
  sorry

theorem map_example : Eq (List Nat) (map Nat Nat Nat.succ l12)
    (List.cons Nat two (List.cons Nat three (List.nil Nat))) :=
  sorry

theorem nil_append : ∀ (A : Type) (l : List A), Eq (List A) (append A (List.nil A) l) l :=
  sorry

-- ---- induction on lists ----

theorem append_nil : ∀ (A : Type) (l : List A), Eq (List A) (append A l (List.nil A)) l :=
  sorry

theorem length_append : ∀ (A : Type) (l r : List A),
    Eq Nat (length A (append A l r)) (add (length A r) (length A l)) :=
  sorry

theorem length_map : ∀ (A B : Type) (f : A → B) (l : List A),
    Eq Nat (length B (map A B f l)) (length A l) :=
  sorry
