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
  Eq.refl (List Nat) (List.cons Nat one (List.cons Nat two (List.cons Nat three (List.nil Nat))))

theorem map_example : Eq (List Nat) (map Nat Nat Nat.succ l12)
    (List.cons Nat two (List.cons Nat three (List.nil Nat))) :=
  Eq.refl (List Nat) (List.cons Nat two (List.cons Nat three (List.nil Nat)))

theorem nil_append : ∀ (A : Type) (l : List A), Eq (List A) (append A (List.nil A) l) l :=
  fun (A : Type) (l : List A) => Eq.refl (List A) l

-- ---- induction on lists ----

theorem append_nil : ∀ (A : Type) (l : List A), Eq (List A) (append A l (List.nil A)) l :=
  fun (A : Type) (l : List A) =>
    List.rec.{0} A (fun (k : List A) => Eq (List A) (append A k (List.nil A)) k)
      (Eq.refl (List A) (List.nil A))
      (fun (x : A) (xs : List A) (ih : Eq (List A) (append A xs (List.nil A)) xs) =>
        Eq.rec.{0} (List A) (append A xs (List.nil A))
          (fun (ys : List A) (_ : Eq (List A) (append A xs (List.nil A)) ys) =>
            Eq (List A) (List.cons A x (append A xs (List.nil A))) (List.cons A x ys))
          (Eq.refl (List A) (List.cons A x (append A xs (List.nil A)))) xs ih)
      l

theorem length_append : ∀ (A : Type) (l r : List A),
    Eq Nat (length A (append A l r)) (add (length A r) (length A l)) :=
  fun (A : Type) (l r : List A) =>
    List.rec.{0} A (fun (k : List A) => Eq Nat (length A (append A k r)) (add (length A r) (length A k)))
      (Eq.refl Nat (length A r))
      (fun (x : A) (xs : List A) (ih : Eq Nat (length A (append A xs r)) (add (length A r) (length A xs))) =>
        Eq.rec.{0} Nat (length A (append A xs r))
          (fun (n : Nat) (_ : Eq Nat (length A (append A xs r)) n) =>
            Eq Nat (Nat.succ (length A (append A xs r))) (Nat.succ n))
          (Eq.refl Nat (Nat.succ (length A (append A xs r)))) (add (length A r) (length A xs)) ih)
      l

theorem length_map : ∀ (A B : Type) (f : A → B) (l : List A),
    Eq Nat (length B (map A B f l)) (length A l) :=
  fun (A B : Type) (f : A → B) (l : List A) =>
    List.rec.{0} A (fun (k : List A) => Eq Nat (length B (map A B f k)) (length A k))
      (Eq.refl Nat Nat.zero)
      (fun (x : A) (xs : List A) (ih : Eq Nat (length B (map A B f xs)) (length A xs)) =>
        Eq.rec.{0} Nat (length B (map A B f xs))
          (fun (n : Nat) (_ : Eq Nat (length B (map A B f xs)) n) =>
            Eq Nat (Nat.succ (length B (map A B f xs))) (Nat.succ n))
          (Eq.refl Nat (Nat.succ (length B (map A B f xs)))) (length A xs) ih)
      l
