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
	JConv     = 5 // Γ ⊢ t : T,  T ≡βι T',  Γ ⊢ T' : s  ⇒  Γ ⊢ t : T'
	JConst    = 6 // Γ ⊢ c.{u} : Type(c)[BVar 0 := Sort u]   (constant table lookup)
	NumJRules = 7
)

// Conversion (βι-equivalence) rules.
const (
	CRefl     = 0
	CSym      = 1
	CTrans    = 2
	CBeta     = 3 // (λx:A.b) a ≡ b[a]
	CPi       = 4 // congruence, bodies opened with a fresh free variable
	CLam      = 5
	CApp      = 6
	CIota     = 7 // rec ps P ms is (c qs fs) ≡ Rhs(c) rec ps P ms fs   (via an iota walk)
	NumCRules = 8
)

// ConstRow is one row of the *public* constant table, generated from the
// inductive declarations of the public file.
//
//	Type: the constant's type. For a recursor that eliminates into any
//	      universe, BVar 0 stands for the motive's universe `Sort u`, and the
//	      constant `c.{u}` has type Type[BVar 0 := Sort u].
//
// The remaining fields are only meaningful for constructors (Ctor = 1) and
// describe the ι-rule of that constructor:
//
//	rec a_1 … a_NRec (c b_1 … b_NCA)  ≡  Rhs rec a_1 … a_NPre b_{NCP+1} … b_NCA
//
// where Rhs = fun r ps motive minors fields => minor_c fields ihs is a closed
// term whose recursive calls go through its first argument r.
type ConstRow struct {
	Type       int
	Ctor       int // 1 iff this constant is a constructor
	Rec        int // constructor: constant index of its recursor
	Rhs        int // constructor: ι right-hand side (closed term)
	NPre, NRec int // recursor arguments kept by ι / before the major premise
	NCP, NCA   int // constructor parameters / all constructor arguments
}

// Iota walk rows. A walk proves, one argument per row, that
//
//	U = rec a_1 … a_N,   W = Rhs rec a_1 … a_min(N,NPre)           (rec phase)
//	M = c b_1 … b_N,     W = (rec-phase W) b_{NCP+1} … b_N          (ctor phase)
//
// so that the final row justifies the CIota conversion App(U, M) ≡ W.
const (
	WPad      = 0
	WRecBase  = 1
	WRecArg   = 2
	WCtorBase = 3
	WCtorArg  = 4
	NumWKinds = 5
)

type IotaRow struct{ Kind, Ctor, U, M, W, N, Prev, Keep int }

// CtxRow: context node = parent context extended with one hypothesis.
// Row 0 is the empty context.
type CtxRow struct{ Parent, Type, Depth int }

// LookRow: "the free variable of level Lvl has type Ty in context Ctx".
type LookRow struct{ Ctx, Lvl, Ty, Base, Next int }

// InstRow: Inst(T, K, S) = R   (replace BVar K by S); C1, C2 are child rows.
// Skip=1: G(T) <= K, so BVar K does not occur and R = T.
type InstRow struct{ T, K, S, R, C1, C2, Skip int }

// ConvRow: T1 ≡β T2 by Rule.
// For CIota, I1 is the index of the final iota-walk row.
type ConvRow struct{ Rule, T1, T2, C1, C2, I1, I2, V, M int }

// JudRow: Ctx ⊢ Subj : Ty by Rule.
type JudRow struct {
	Rule, Ctx, Subj, Ty int
	C1, C2              int // child judgments
	I1, I2              int // instantiation rows (opening binders / β)
	X                   int // extended context (Pi/Lam)
	V                   int // fresh free-variable term (Pi/Lam); `Sort u` (Const)
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
	NK int // constant-table rows (public)
	NW int // iota-walk rows
	NB int // bit-width for range checks
}

var (
	SmallSizes   = Sizes{NP: 256, NT: 768, NX: 64, NL: 128, NI: 512, NC: 128, NJ: 192, NK: 32, NW: 64, NB: 16}
	DefaultSizes = Sizes{NP: 384, NT: 1280, NX: 192, NL: 320, NI: 1024, NC: 320, NJ: 640, NK: 64, NW: 128, NB: 16}
	LargeSizes   = Sizes{NP: 512, NT: 4096, NX: 512, NL: 1024, NI: 4096, NC: 1024, NJ: 2048, NK: 64, NW: 512, NB: 16}
	Profiles     = map[string]Sizes{"small": SmallSizes, "default": DefaultSizes, "large": LargeSizes}
)

type Certificate struct {
	S      *Store
	Root   int // public: id of the theorem statement
	Ctx    []CtxRow
	Look   []LookRow
	Inst   []InstRow
	Conv   []ConvRow
	Jud    []JudRow
	Iota   []IotaRow
	Padded bool
}

// Usage reports how many rows of each table the certificate uses.
func (c *Certificate) Usage() map[string]int {
	return map[string]int{
		"terms": len(c.S.Nodes), "ctx": len(c.Ctx), "lookups": len(c.Look),
		"inst": len(c.Inst), "conv": len(c.Conv), "judgments": len(c.Jud), "iota": len(c.Iota),
	}
}
