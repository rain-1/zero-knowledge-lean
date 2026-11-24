package kernel

import (
	"math/rand"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func loadEnv(t *testing.T) *Env {
	src, err := os.ReadFile("../examples/logic.lean")
	if err != nil {
		t.Fatal(err)
	}
	env, err := Parse(string(src))
	if err != nil {
		t.Fatal(err)
	}
	return env
}

func TestCertifyAllTheorems(t *testing.T) {
	env := loadEnv(t)
	for _, d := range env.Decls {
		if d.Kind != "theorem" {
			continue
		}
		c, err := Certify(env.S, d.Type, d.Value, DefaultSizes)
		if err != nil {
			t.Fatalf("%s: %v", d.Name, err)
		}
		t.Logf("%-16s usage %v", d.Name, c.Usage())
		if err := c.Pad(DefaultSizes); err != nil {
			t.Fatalf("%s: %v", d.Name, err)
		}
		if err := c.Relation(DefaultSizes); err != nil {
			t.Fatalf("%s: relation: %v", d.Name, err)
		}
	}
}

func TestRejectsBadProofs(t *testing.T) {
	bad := []string{
		// wrong order of arguments
		`def And (A B : Prop) : Prop := ∀ (C : Prop), (A → B → C) → C
		 theorem bad : ∀ (A B : Prop), And A B → And B A :=
		   fun (A B : Prop) (h : And A B) (C : Prop) (k : B → A → C) => h C k`,
		// proving False from nothing
		`def False : Prop := ∀ (C : Prop), C
		 theorem bad : False := fun (C : Prop) => C`,
		// Type : Type is rejected
		`theorem bad : Type := Type`,
		// arithmetic error
		`def Eq (A : Type 1) (x y : A) : Prop := ∀ (P : A → Prop), P x → P y
		 def Nat : Type 1 := ∀ (X : Type), (X → X) → X → X
		 def zero : Nat := fun (X : Type) (s : X → X) (z : X) => z
		 def succ (n : Nat) : Nat := fun (X : Type) (s : X → X) (z : X) => s (n X s z)
		 def add (m n : Nat) : Nat := fun (X : Type) (s : X → X) (z : X) => m X s (n X s z)
		 theorem bad : Eq Nat (add (succ zero) (succ zero)) (succ zero) :=
		   fun (P : Nat → Prop) (h : P (add (succ zero) (succ zero))) => h`,
	}
	for i, src := range bad {
		env, err := Parse(src)
		if err != nil {
			t.Fatalf("case %d parse: %v", i, err)
		}
		d := env.Decls[len(env.Decls)-1]
		if _, err := Certify(env.S, d.Type, d.Value, DefaultSizes); err == nil {
			t.Fatalf("case %d: bad proof accepted", i)
		} else {
			t.Logf("case %d rejected: %v", i, strings.Split(err.Error(), "\n")[0])
		}
	}
}

func TestPublicSource(t *testing.T) {
	env := loadEnv(t)
	pub := env.PublicSource()
	penv, err := Parse(pub)
	if err != nil {
		t.Fatal(err)
	}
	for _, d := range penv.Decls {
		if d.Kind == "theorem" && d.Value >= 0 {
			t.Fatalf("%s: proof leaked into public source", d.Name)
		}
		// statements must lay out identically
		od, _ := env.Lookup(d.Name)
		s1, r1, _ := PublicLayout(env.S, od.Type, DefaultSizes, map[int]int{})
		s2, r2, _ := PublicLayout(penv.S, d.Type, DefaultSizes, map[int]int{})
		if r1 != r2 {
			t.Fatalf("%s: root differs", d.Name)
		}
		for i := 0; i < DefaultSizes.NP; i++ {
			if s1.Nodes[i] != s2.Nodes[i] {
				t.Fatalf("%s: public row %d differs", d.Name, i)
			}
		}
	}
}

// Soundness fuzzing of the relation: randomly corrupt witness fields of a
// valid certificate. Whenever the relation still accepts, the derivation's
// root subject must still be a genuine proof of the statement according to the
// independent reference checker (Certify).
func TestRelationFuzz(t *testing.T) {
	env := loadEnv(t)
	d, _ := env.Lookup("and_comm")
	rng := rand.New(rand.NewSource(1))
	accepted := 0
	const trials = 3000
	for trial := 0; trial < trials; trial++ {
		c, err := Certify(env.S, d.Type, d.Value, DefaultSizes)
		if err != nil {
			t.Fatal(err)
		}
		if err := c.Pad(DefaultSizes); err != nil {
			t.Fatal(err)
		}
		mutate(c, rng)
		if c.Relation(DefaultSizes) != nil {
			continue
		}
		accepted++
		root := c.Jud[len(c.Jud)-1]
		// independent re-check of the (possibly changed) proof term
		if _, err := Certify(c.S, c.Root, root.Subj, DefaultSizes); err != nil {
			t.Fatalf("trial %d: relation accepted a certificate whose root term is not a proof: %v", trial, err)
		}
	}
	t.Logf("%d/%d mutated certificates still satisfied the relation (all re-verified sound)", accepted, trials)
}

func mutate(c *Certificate, r *rand.Rand) {
	small := func() int { return r.Intn(8) - 1 }
	pick := func(n int) int {
		// bias towards used rows (the low indices)
		if r.Intn(2) == 0 {
			return r.Intn(min(n, 64))
		}
		return r.Intn(n)
	}
	nmut := 1 + r.Intn(3)
	for k := 0; k < nmut; k++ {
		switch r.Intn(6) {
		case 0:
			i := DefaultSizes.NP + pick(len(c.S.Nodes)-DefaultSizes.NP)
			n := &c.S.Nodes[i]
			switch r.Intn(5) {
			case 0:
				n.Tag = r.Intn(6)
			case 1:
				n.A = r.Intn(i + 1)
			case 2:
				n.B = r.Intn(i + 1)
			case 3:
				n.F += small()
			case 4:
				n.G += small()
			}
		case 1:
			i := pick(len(c.Jud))
			j := &c.Jud[i]
			f := []*int{&j.Rule, &j.Ctx, &j.Subj, &j.Ty, &j.C1, &j.C2, &j.I1, &j.I2, &j.X, &j.V, &j.L, &j.Cv, &j.M}
			*f[r.Intn(len(f))] = r.Intn(i + 3)
		case 2:
			i := pick(len(c.Inst))
			j := &c.Inst[i]
			f := []*int{&j.T, &j.K, &j.S, &j.R, &j.C1, &j.C2, &j.Skip}
			*f[r.Intn(len(f))] = r.Intn(i + 3)
		case 3:
			i := pick(len(c.Conv))
			j := &c.Conv[i]
			f := []*int{&j.Rule, &j.T1, &j.T2, &j.C1, &j.C2, &j.I1, &j.I2, &j.V, &j.M}
			*f[r.Intn(len(f))] = r.Intn(i + 3)
		case 4:
			i := pick(len(c.Look))
			j := &c.Look[i]
			f := []*int{&j.Ctx, &j.Lvl, &j.Ty, &j.Base, &j.Next}
			*f[r.Intn(len(f))] = r.Intn(i + 3)
		case 5:
			i := 1 + pick(len(c.Ctx)-1)
			j := &c.Ctx[i]
			f := []*int{&j.Parent, &j.Type, &j.Depth}
			*f[r.Intn(len(f))] = r.Intn(i + 3)
		}
	}
}

func loadFile(t *testing.T, path string) *Env {
	src, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	env, err := Parse(string(src))
	if err != nil {
		t.Fatal(err)
	}
	return env
}

func TestInductiveTheorems(t *testing.T) {
	env := loadFile(t, "../examples/inductive.lean")
	sawIota := false
	for _, d := range env.Decls {
		if d.Kind != "theorem" {
			continue
		}
		c, err := Certify(env.S, d.Type, d.Value, DefaultSizes)
		if err != nil {
			t.Fatalf("%s: %v", d.Name, err)
		}
		t.Logf("%-14s usage %v", d.Name, c.Usage())
		sawIota = sawIota || len(c.Iota) > 0
		if err := c.Pad(DefaultSizes); err != nil {
			t.Fatalf("%s: %v", d.Name, err)
		}
		if err := c.Relation(DefaultSizes); err != nil {
			t.Fatalf("%s: relation: %v", d.Name, err)
		}
	}
	if !sawIota {
		t.Fatal("no theorem used ι-reduction")
	}
}

func TestInductivePublicSource(t *testing.T) {
	env := loadFile(t, "../examples/inductive.lean")
	penv, err := Parse(env.PublicSource())
	if err != nil {
		t.Fatal(err)
	}
	for _, d := range penv.Decls {
		if d.Kind != "theorem" {
			continue
		}
		od, _ := env.Lookup(d.Name)
		s1, r1, err1 := PublicLayout(env.S, od.Type, DefaultSizes, map[int]int{})
		s2, r2, err2 := PublicLayout(penv.S, d.Type, DefaultSizes, map[int]int{})
		if err1 != nil || err2 != nil || r1 != r2 {
			t.Fatalf("%s: layouts differ (%v, %v)", d.Name, err1, err2)
		}
		for i := 0; i < DefaultSizes.NP; i++ {
			if s1.Nodes[i] != s2.Nodes[i] {
				t.Fatalf("%s: public row %d differs", d.Name, i)
			}
		}
		for i := range s1.Consts {
			if s1.Consts[i] != s2.Consts[i] {
				t.Fatalf("%s: constant %d differs", d.Name, i)
			}
		}
	}
}

func TestRejectsBadInductives(t *testing.T) {
	const prelude = `inductive Nat : Type where | zero : Nat | succ (n : Nat) : Nat
	inductive Eq (A : Type) (a : A) : A → Prop where | refl : Eq A a a
	inductive Ex (A : Type) (P : A → Prop) : Prop where | intro (w : A) (h : P w) : Ex A P
	`
	bad := map[string]string{
		"negative occurrence":      `inductive Bad : Type where | mk (f : Bad → Nat) : Bad`,
		"non-strictly positive":    `inductive Bad : Type where | mk (f : (Bad → Nat) → Nat) : Bad`,
		"universe too large":       `inductive Big : Type where | mk (A : Type) : Big`,
		"wrong result type":        `inductive Bad : Type where | mk : Nat`,
		"parameters changed":       `inductive L (A : Type) : Type where | mk (x : L Nat) : L A`,
		"inductive in index":       `inductive I : Type → Type where | mk : I (I Nat)`,
		"not a sort":               `inductive Bad : Nat where`,
		"missing level":            `def f (n : Nat) : Nat := Nat.rec (fun (_ : Nat) => Nat) n (fun (k r : Nat) => r) n`,
		"small elim into Type":     `def w (A : Type) (P : A → Prop) (h : Ex A P) : A := Ex.rec.{1} A P (fun (_ : Ex A P) => A) (fun (w : A) (p : P w) => w) h`,
		"level on non-recursor":    `def z : Nat := Nat.zero.{1}`,
		"duplicate constructor":    `inductive B : Type where | t : B | t : B`,
		"constructor name clashes": `inductive Nat.zero : Type where`,
	}
	for name, src := range bad {
		if _, err := Parse(prelude + src); err == nil {
			t.Fatalf("%s: accepted", name)
		} else {
			t.Logf("%s: %v", name, err)
		}
	}
	// ill-typed proofs that need ι to refute
	badProofs := []string{
		`def add (m n : Nat) : Nat := Nat.rec.{1} (fun (_ : Nat) => Nat) m (fun (k ih : Nat) => Nat.succ ih) n
		 theorem bad : Eq Nat (add (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (Nat.succ Nat.zero) :=
		   Eq.refl Nat (Nat.succ Nat.zero)`,
		`theorem bad : Eq Nat Nat.zero (Nat.succ Nat.zero) := Eq.refl Nat Nat.zero`,
	}
	for i, src := range badProofs {
		env, err := Parse(prelude + src)
		if err != nil {
			t.Fatalf("bad proof %d: parse: %v", i, err)
		}
		d := env.Decls[len(env.Decls)-1]
		if _, err := Certify(env.S, d.Type, d.Value, DefaultSizes); err == nil {
			t.Fatalf("bad proof %d accepted", i)
		}
	}
}

// Relation fuzzing on a certificate that uses constants and ι-reduction.
func TestRelationFuzzInductive(t *testing.T) {
	env := loadFile(t, "../examples/inductive.lean")
	d, _ := env.Lookup("true_ne_false")
	rng := rand.New(rand.NewSource(2))
	accepted := 0
	const trials = 3000
	for trial := 0; trial < trials; trial++ {
		c, err := Certify(env.S, d.Type, d.Value, DefaultSizes)
		if err != nil {
			t.Fatal(err)
		}
		used := len(c.Iota)
		if err := c.Pad(DefaultSizes); err != nil {
			t.Fatal(err)
		}
		if trial%2 == 0 {
			mutate(c, rng)
		} else {
			for k := 0; k < 1+rng.Intn(2); k++ {
				w := &c.Iota[rng.Intn(used)]
				f := []*int{&w.Kind, &w.Ctor, &w.U, &w.M, &w.W, &w.N, &w.Prev, &w.Keep}
				*f[rng.Intn(len(f))] += rng.Intn(5) - 2
			}
		}
		if c.Relation(DefaultSizes) != nil {
			continue
		}
		accepted++
		root := c.Jud[len(c.Jud)-1]
		if _, err := Certify(c.S, c.Root, root.Subj, DefaultSizes); err != nil {
			t.Fatalf("trial %d: relation accepted a certificate whose root term is not a proof: %v", trial, err)
		}
	}
	t.Logf("%d/%d mutated certificates still satisfied the relation (all re-verified sound)", accepted, trials)
}

func TestIndexedAndInfinitaryRecursors(t *testing.T) {
	const src = `inductive Nat : Type where | zero : Nat | succ (n : Nat) : Nat
	inductive Eq (A : Type) (a : A) : A → Prop where | refl : Eq A a a
	inductive Vec (A : Type) : Nat → Type where
	  | nil : Vec A Nat.zero
	  | cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (Nat.succ n)
	def len (A : Type) (n : Nat) (v : Vec A n) : Nat :=
	  Vec.rec.{1} A (fun (m : Nat) (_ : Vec A m) => Nat) Nat.zero
	    (fun (m : Nat) (x : A) (xs : Vec A m) (ih : Nat) => Nat.succ ih) n v
	inductive Tree : Type where | leaf : Tree | node (f : Nat → Tree) : Tree
	def leftDepth (t : Tree) : Nat :=
	  Tree.rec.{1} (fun (_ : Tree) => Nat) Nat.zero
	    (fun (f : Nat → Tree) (ih : Nat → Nat) => Nat.succ (ih Nat.zero)) t
	def one : Nat := Nat.succ Nat.zero
	def two : Nat := Nat.succ one
	def v2 : Vec Nat two := Vec.cons Nat one Nat.zero (Vec.cons Nat Nat.zero one (Vec.nil Nat))
	def t2 : Tree := Tree.node (fun (n : Nat) => Tree.node (fun (m : Nat) => Tree.leaf))
	theorem len_v2 : Eq Nat (len Nat two v2) two := Eq.refl Nat two
	theorem depth_t2 : Eq Nat (leftDepth t2) two := Eq.refl Nat two
	theorem bad_len : Eq Nat (len Nat two v2) one := Eq.refl Nat one
	theorem bad_depth : Eq Nat (leftDepth t2) one := Eq.refl Nat one
	`
	env, err := Parse(src)
	if err != nil {
		t.Fatal(err)
	}
	sz := DefaultSizes
	sz.NI, sz.NC, sz.NJ, sz.NT = 4096, 1024, 2048, 4096
	for _, name := range []string{"len_v2", "depth_t2", "bad_len", "bad_depth"} {
		d, _ := env.Lookup(name)
		c, err := Certify(env.S, d.Type, d.Value, sz)
		if strings.HasPrefix(name, "bad") {
			if err == nil {
				t.Fatalf("%s accepted", name)
			}
			continue
		}
		if err != nil {
			t.Fatalf("%s: %v", name, err)
		}
		if err := c.Pad(sz); err != nil {
			t.Fatalf("%s: %v", name, err)
		}
		if err := c.Relation(sz); err != nil {
			t.Fatalf("%s: relation: %v", name, err)
		}
	}
}

// Every theorem in every example file certifies, satisfies the relation at the
// smallest profile it fits, and its public statement lays out identically.
func TestAllExamples(t *testing.T) {
	files, err := filepath.Glob("../examples/*.lean")
	if err != nil {
		t.Fatal(err)
	}
	for _, f := range files {
		if strings.HasSuffix(f, ".public.lean") {
			continue
		}
		env := loadFile(t, f)
		penv, err := Parse(env.PublicSource())
		if err != nil {
			t.Fatalf("%s: public source: %v", f, err)
		}
		for _, d := range env.Decls {
			if d.Kind != "theorem" {
				continue
			}
			var fit string
			for _, p := range []string{"small", "default", "large"} {
				sz := Profiles[p]
				c, err := Certify(env.S, d.Type, d.Value, sz)
				if err != nil {
					if strings.Contains(err.Error(), "capacity") {
						continue
					}
					t.Fatalf("%s %s: %v", f, d.Name, err)
				}
				if c.Pad(sz) != nil {
					continue
				}
				if err := c.Relation(sz); err != nil {
					t.Fatalf("%s %s: relation: %v", f, d.Name, err)
				}
				pd, _ := penv.Lookup(d.Name)
				s1, r1, _ := PublicLayout(env.S, d.Type, sz, map[int]int{})
				s2, r2, err := PublicLayout(penv.S, pd.Type, sz, map[int]int{})
				if err != nil || r1 != r2 || len(s1.Consts) != len(s2.Consts) {
					t.Fatalf("%s %s: public layout differs", f, d.Name)
				}
				for i := range s1.Nodes {
					if s1.Nodes[i] != s2.Nodes[i] {
						t.Fatalf("%s %s: public row %d differs", f, d.Name, i)
					}
				}
				fit = p
				break
			}
			if fit == "" {
				t.Fatalf("%s %s: exceeds every profile", f, d.Name)
			}
			t.Logf("%-28s %-16s %s", filepath.Base(f), d.Name, fit)
		}
	}
}
