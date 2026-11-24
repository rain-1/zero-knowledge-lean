/- Basic data types: Bool, Option, Prod, Sum and Sigma, with projections,
   case analysis and the laws that need induction (there is no η). -/

inductive False : Prop where
inductive True : Prop where
  | intro : True
def Not (A : Prop) : Prop := A → False

inductive Eq (A : Type) (a : A) : A → Prop where
  | refl : Eq A a a

inductive Bool : Type where
  | false : Bool
  | true : Bool

inductive Option (A : Type) : Type where
  | none : Option A
  | some (x : A) : Option A

inductive Prod (A B : Type) : Type where
  | mk (a : A) (b : B) : Prod A B

inductive Sum (A B : Type) : Type where
  | inl (a : A) : Sum A B
  | inr (b : B) : Sum A B

-- dependent pairs: the type of the second component depends on the first
inductive Sigma (A : Type) (B : A → Type) : Type where
  | mk (a : A) (b : B a) : Sigma A B

def not (b : Bool) : Bool := Bool.rec.{1} (fun (_ : Bool) => Bool) Bool.true Bool.false b
def and (a b : Bool) : Bool := Bool.rec.{1} (fun (_ : Bool) => Bool) Bool.false b a

def fst (A B : Type) (p : Prod A B) : A := Prod.rec.{1} A B (fun (_ : Prod A B) => A) (fun (a : A) (b : B) => a) p
def snd (A B : Type) (p : Prod A B) : B := Prod.rec.{1} A B (fun (_ : Prod A B) => B) (fun (a : A) (b : B) => b) p
def swap (A B : Type) (p : Prod A B) : Prod B A :=
  Prod.rec.{1} A B (fun (_ : Prod A B) => Prod B A) (fun (a : A) (b : B) => Prod.mk B A b a) p

def getD (A : Type) (d : A) (o : Option A) : A :=
  Option.rec.{1} A (fun (_ : Option A) => A) d (fun (x : A) => x) o

def Sum.swap (A B : Type) (s : Sum A B) : Sum B A :=
  Sum.rec.{1} A B (fun (_ : Sum A B) => Sum B A) (fun (a : A) => Sum.inr B A a) (fun (b : B) => Sum.inl B A b) s

-- ---- Bool ----

theorem not_not : ∀ (b : Bool), Eq Bool (not (not b)) b :=
  sorry

theorem and_false : ∀ (b : Bool), Eq Bool (and b Bool.false) Bool.false :=
  sorry

theorem true_ne_false : Not (Eq Bool Bool.true Bool.false) :=
  sorry

-- ---- Prod ----

theorem fst_mk : ∀ (A B : Type) (a : A) (b : B), Eq A (fst A B (Prod.mk A B a b)) a :=
  sorry

theorem swap_swap : ∀ (A B : Type) (p : Prod A B), Eq (Prod A B) (swap B A (swap A B p)) p :=
  sorry

theorem eta_prod : ∀ (A B : Type) (p : Prod A B), Eq (Prod A B) (Prod.mk A B (fst A B p) (snd A B p)) p :=
  sorry

-- ---- Option / Sum ----

theorem getD_some : ∀ (A : Type) (d x : A), Eq A (getD A d (Option.some A x)) x :=
  sorry

theorem sum_swap_swap : ∀ (A B : Type) (s : Sum A B), Eq (Sum A B) (Sum.swap B A (Sum.swap A B s)) s :=
  sorry

-- ---- Sigma ----

theorem sigma_first : ∀ (A : Type) (B : A → Type) (a : A) (b : B a),
    Eq A (Sigma.rec.{1} A B (fun (_ : Sigma A B) => A) (fun (x : A) (y : B x) => x) (Sigma.mk A B a b)) a :=
  sorry
