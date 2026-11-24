/- zkLean example library: Church-encoded logic and arithmetic.
   `def`s are public (they are part of what a statement means);
   theorem bodies are private witnesses. -/

def False : Prop := ∀ (C : Prop), C
def True  : Prop := ∀ (C : Prop), C → C
def Not (A : Prop) : Prop := A → False
def And (A B : Prop) : Prop := ∀ (C : Prop), (A → B → C) → C
def Or  (A B : Prop) : Prop := ∀ (C : Prop), (A → C) → (B → C) → C
def Iff (A B : Prop) : Prop := And (A → B) (B → A)

theorem trivial : True := fun (C : Prop) (c : C) => c

theorem modus_ponens : ∀ (A B : Prop), A → (A → B) → B :=
  fun (A B : Prop) (a : A) (f : A → B) => f a

theorem and_comm : ∀ (A B : Prop), And A B → And B A :=
  fun (A B : Prop) (h : And A B) (C : Prop) (k : B → A → C) =>
    h C (fun (a : A) (b : B) => k b a)

theorem or_comm : ∀ (A B : Prop), Or A B → Or B A :=
  fun (A B : Prop) (h : Or A B) (C : Prop) (l : B → C) (r : A → C) => h C r l

theorem contrapositive : ∀ (A B : Prop), (A → B) → Not B → Not A :=
  fun (A B : Prop) (f : A → B) (nb : Not B) (a : A) => nb (f a)

theorem dni : ∀ (A : Prop), A → Not (Not A) :=
  fun (A : Prop) (a : A) (na : Not A) => na a

theorem not_or_iff : ∀ (A B : Prop), Iff (Not (Or A B)) (And (Not A) (Not B)) :=
  fun (A B : Prop) (C : Prop)
      (k : (Not (Or A B) → And (Not A) (Not B)) → (And (Not A) (Not B) → Not (Or A B)) → C) =>
    k (fun (h : Not (Or A B)) (D : Prop) (m : Not A → Not B → D) =>
          m (fun (a : A) => h (fun (E : Prop) (l : A → E) (r : B → E) => l a))
            (fun (b : B) => h (fun (E : Prop) (l : A → E) (r : B → E) => r b)))
      (fun (h : And (Not A) (Not B)) (o : Or A B) =>
          o False (fun (a : A) => h False (fun (na : Not A) (nb : Not B) => na a))
                  (fun (b : B) => h False (fun (na : Not A) (nb : Not B) => nb b)))

-- Leibniz equality and Church numerals (Nat lives in Type 1)
def Eq (A : Type 1) (x y : A) : Prop := ∀ (P : A → Prop), P x → P y
def Nat : Type 1 := ∀ (X : Type), (X → X) → X → X
def zero : Nat := fun (X : Type) (s : X → X) (z : X) => z
def succ (n : Nat) : Nat := fun (X : Type) (s : X → X) (z : X) => s (n X s z)
def add (m n : Nat) : Nat := fun (X : Type) (s : X → X) (z : X) => m X s (n X s z)
def mul (m n : Nat) : Nat := fun (X : Type) (s : X → X) (z : X) => m X (n X s) z
def two  : Nat := succ (succ zero)
def three : Nat := succ two
def four : Nat := succ (succ two)
def six  : Nat := add three three

theorem eq_symm : ∀ (A : Type 1) (x y : A), Eq A x y → Eq A y x :=
  fun (A : Type 1) (x y : A) (h : Eq A x y) => h (fun (z : A) => Eq A z x) (fun (P : A → Prop) (p : P x) => p)

theorem two_plus_two : Eq Nat (add two two) four :=
  fun (P : Nat → Prop) (h : P (add two two)) => h

theorem two_times_three : Eq Nat (mul two three) six :=
  fun (P : Nat → Prop) (h : P (mul two three)) => h
