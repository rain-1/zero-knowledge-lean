/- zkLean example library: Church-encoded logic and arithmetic.
   `def`s are public (they are part of what a statement means);
   theorem bodies are private witnesses. -/

def False : Prop := ∀ (C : Prop), C
def True  : Prop := ∀ (C : Prop), C → C
def Not (A : Prop) : Prop := A → False
def And (A B : Prop) : Prop := ∀ (C : Prop), (A → B → C) → C
def Or  (A B : Prop) : Prop := ∀ (C : Prop), (A → C) → (B → C) → C
def Iff (A B : Prop) : Prop := And (A → B) (B → A)

theorem trivial : True := sorry

theorem modus_ponens : ∀ (A B : Prop), A → (A → B) → B :=
  sorry

theorem and_comm : ∀ (A B : Prop), And A B → And B A :=
  sorry

theorem or_comm : ∀ (A B : Prop), Or A B → Or B A :=
  sorry

theorem contrapositive : ∀ (A B : Prop), (A → B) → Not B → Not A :=
  sorry

theorem dni : ∀ (A : Prop), A → Not (Not A) :=
  sorry

theorem not_or_iff : ∀ (A B : Prop), Iff (Not (Or A B)) (And (Not A) (Not B)) :=
  sorry

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
  sorry

theorem two_plus_two : Eq Nat (add two two) four :=
  sorry

theorem two_times_three : Eq Nat (mul two three) six :=
  sorry
