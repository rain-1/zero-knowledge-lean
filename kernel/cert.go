package kernel

// A Certificate is a flattened, *locally checkable* typing derivation.
//
// Every row of every table can be validated by looking only at a constant
// number of other rows (via their indices), and every reference points to a
// strictly earlier row of the same table. That makes the whole relation a
// fixed-shape arithmetic circuit with random-access lookups; see
// circuit/circuit.go (in-circuit) and Relation() below (native mirror).

// Judgment rules.
const (
	JSort     = 0 // ⊢ Sort u : Sort (u+1)
	JVar      = 1 // (x : A) ∈ Γ  ⇒  Γ ⊢ x : A
	JPi       = 2 // Γ ⊢ A : Sort u,  Γ,x:A ⊢ B[x] : Sort v  ⇒  Γ ⊢ Πx:A.B : Sort (imax u v)
	JLam      = 3 // Γ ⊢ Πx:A.B : s,  Γ,x:A ⊢ b[x] : B[x]  ⇒  Γ ⊢ λx:A.b : Πx:A.B
	JApp      = 4 // Γ ⊢ f : Πx:A.B,  Γ ⊢ a : A  ⇒  Γ ⊢ f a : B[a]
	JConv     = 5 // Γ ⊢ t : T,  T ≡β T',  Γ ⊢ T' : s  ⇒  Γ ⊢ t : T'
	NumJRules = 6
)

// Conversion (β-equivalence) rules.
const (
	CRefl     = 0
	CSym      = 1
	CTrans    = 2
	CBeta     = 3 // (λx:A.b) a ≡ b[a]
	CPi       = 4 // congruence, bodies opened with a fresh free variable
	CLam      = 5
	CApp      = 6
	NumCRules = 7
)

// CtxRow: context node = parent context extended with one hypothesis.
// Row 0 is the empty context.
type CtxRow struct{ Parent, Type, Depth int }

// LookRow: "the free variable of level Lvl has type Ty in context Ctx".
type LookRow struct{ Ctx, Lvl, Ty, Base, Next int }

// InstRow: Inst(T, K, S) = R   (replace BVar K by S); C1, C2 are child rows.
// Skip=1: G(T) <= K, so BVar K does not occur and R = T.
type InstRow struct{ T, K, S, R, C1, C2, Skip int }

// ConvRow: T1 ≡β T2 by Rule.
type ConvRow struct{ Rule, T1, T2, C1, C2, I1, I2, V, M int }

// JudRow: Ctx ⊢ Subj : Ty by Rule.
type JudRow struct {
	Rule, Ctx, Subj, Ty int
	C1, C2              int // child judgments
	I1, I2              int // instantiation rows (opening binders / β)
	X                   int // extended context (Pi/Lam)
	V                   int // fresh free-variable term (Pi/Lam)
	L                   int // context lookup row (Var)
	Cv                  int // conversion row (Conv)
	M                   int // max(u, v) witness (Pi)
}

// Sizes are the fixed capacities of the circuit. A proof reveals only these.
type Sizes struct {
	NP int // public term rows (the theorem statement)
	NT int // total term rows (public + private)
	NX int // context rows
	NL int // context-lookup rows
	NI int // instantiation rows
	NC int // conversion rows
	NJ int // judgment rows
	NB int // bit-width for range checks
}

var (
	SmallSizes   = Sizes{NP: 64, NT: 512, NX: 64, NL: 128, NI: 512, NC: 128, NJ: 192, NB: 16}
	DefaultSizes = Sizes{NP: 96, NT: 1024, NX: 192, NL: 320, NI: 1024, NC: 320, NJ: 640, NB: 16}
	Profiles     = map[string]Sizes{"small": SmallSizes, "default": DefaultSizes}
)

type Certificate struct {
	S      *Store
	Root   int // public: id of the theorem statement
	Ctx    []CtxRow
	Look   []LookRow
	Inst   []InstRow
	Conv   []ConvRow
	Jud    []JudRow
	Padded bool
}

// Usage reports how many rows of each table the certificate uses.
func (c *Certificate) Usage() map[string]int {
	return map[string]int{
		"terms": len(c.S.Nodes), "ctx": len(c.Ctx), "lookups": len(c.Look),
		"inst": len(c.Inst), "conv": len(c.Conv), "judgments": len(c.Jud),
	}
}
