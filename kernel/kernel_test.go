package kernel

import (
	"math/rand"
	"os"
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
		c, err := Certify(env.S, d.Type, d.Value, DefaultSizes.NP)
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
		if _, err := Certify(env.S, d.Type, d.Value, DefaultSizes.NP); err == nil {
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
		s1, r1, _ := PublicLayout(env.S, od.Type, DefaultSizes.NP, map[int]int{})
		s2, r2, _ := PublicLayout(penv.S, d.Type, DefaultSizes.NP, map[int]int{})
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
		c, err := Certify(env.S, d.Type, d.Value, DefaultSizes.NP)
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
		if _, err := Certify(c.S, c.Root, root.Subj, DefaultSizes.NP); err != nil {
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
