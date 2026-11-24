package circuit

import (
	"math/rand"
	"os"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/test"
	"github.com/river/zklean/kernel"
)

var tiny = kernel.SmallSizes

func cert(t *testing.T, name string, sz kernel.Sizes) *kernel.Certificate {
	src, _ := os.ReadFile("../examples/logic.lean")
	env, err := kernel.Parse(string(src))
	if err != nil {
		t.Fatal(err)
	}
	d, _ := env.Lookup(name)
	c, err := kernel.Certify(env.S, d.Type, d.Value, sz.NP)
	if err != nil {
		t.Fatal(err)
	}
	if err := c.Pad(sz); err != nil {
		t.Fatal(err)
	}
	if err := c.Relation(sz); err != nil {
		t.Fatal(err)
	}
	return c
}

func TestCompileSize(t *testing.T) {
	for _, sz := range []kernel.Sizes{tiny, kernel.DefaultSizes} {
		t0 := time.Now()
		ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, New(sz))
		if err != nil {
			t.Fatal(err)
		}
		t.Logf("sizes %+v: %d constraints, %d public, compiled in %v", sz, ccs.GetNbConstraints(), ccs.GetNbPublicVariables(), time.Since(t0))
	}
}

// The honest witness satisfies the circuit.
func TestHonestWitness(t *testing.T) {
	for _, name := range []string{"modus_ponens", "and_comm", "two_plus_two"} {
		sz := tiny
		if name == "two_plus_two" {
			sz = kernel.DefaultSizes
		}
		c := cert(t, name, sz)
		if err := test.IsSolved(New(sz), Assign(c, sz), ecc.BN254.ScalarField()); err != nil {
			t.Fatalf("%s: %v", name, err)
		}
	}
}

// Forged witnesses are rejected by the circuit.
func TestForgedWitnesses(t *testing.T) {
	type forge struct {
		name string
		f    func(c *kernel.Certificate)
	}
	forges := []forge{
		{"claim a different statement", func(c *kernel.Certificate) { c.Root = 0 }},
		{"self-justifying judgment (cycle)", func(c *kernel.Certificate) {
			r := &c.Jud[len(c.Jud)-1]
			r.Rule, r.C1, r.C2 = kernel.JConv, len(c.Jud)-1, len(c.Jud)-1
		}},
		{"variable not in context", func(c *kernel.Certificate) {
			for i := range c.Look {
				if c.Look[i].Base == 1 {
					c.Look[i].Lvl++
					return
				}
			}
		}},
		{"bogus beta step", func(c *kernel.Certificate) {
			for i := range c.Conv {
				if c.Conv[i].Rule == kernel.CBeta {
					c.Conv[i].T2 = c.Conv[i].T1
					return
				}
			}
			panic("no beta row")
		}},
		{"Type : Type", func(c *kernel.Certificate) {
			for i := range c.Jud {
				if c.Jud[i].Rule == kernel.JSort {
					c.Jud[i].Ty = c.Jud[i].Subj
					return
				}
			}
		}},
		{"non-fresh variable in congruence", func(c *kernel.Certificate) {
			for i := range c.Conv {
				r := &c.Conv[i]
				if (r.Rule == kernel.CPi || r.Rule == kernel.CLam) && c.S.N(c.S.N(r.T1).B).F > 0 {
					r.V = c.S.FVar(0)
					return
				}
			}
			panic("no congruence row")
		}},
	}
	for _, fg := range forges {
		c := cert(t, "and_comm", tiny)
		fg.f(c)
		if c.Relation(tiny) == nil {
			t.Fatalf("%s: native relation accepted forgery", fg.name)
		}
		err := test.IsSolved(New(tiny), Assign(c, tiny), ecc.BN254.ScalarField())
		if err == nil {
			t.Fatalf("%s: circuit accepted forgery", fg.name)
		}
		t.Logf("rejected: %s", fg.name)
	}
}

// The circuit must never accept a witness that the native relation rejects
// (the native relation is the documented specification).
func TestCircuitRefinesRelation(t *testing.T) {
	rng := rand.New(rand.NewSource(7))
	agreeAccept, agreeReject := 0, 0
	for trial := 0; trial < 40; trial++ {
		c := cert(t, "and_comm", tiny)
		for k := 0; k < 1+rng.Intn(2); k++ {
			corrupt(c, rng)
		}
		native := c.Relation(tiny) == nil
		var inCircuit bool
		func() {
			defer func() { recover() }()
			inCircuit = test.IsSolved(New(tiny), Assign(c, tiny), ecc.BN254.ScalarField()) == nil
		}()
		if inCircuit && !native {
			t.Fatalf("trial %d: circuit accepted a witness the relation rejects", trial)
		}
		if native && !inCircuit {
			t.Logf("trial %d: circuit stricter than relation (allowed)", trial)
		}
		if native == inCircuit {
			if native {
				agreeAccept++
			} else {
				agreeReject++
			}
		}
	}
	t.Logf("agreement: %d accepted by both, %d rejected by both", agreeAccept, agreeReject)
}

func corrupt(c *kernel.Certificate, r *rand.Rand) {
	j := &c.Jud[r.Intn(85)]
	ins := &c.Inst[r.Intn(216)]
	cv := &c.Conv[r.Intn(40)]
	fields := []*int{&j.Rule, &j.Ctx, &j.Subj, &j.Ty, &j.C1, &j.C2, &j.I1, &j.X, &j.V,
		&ins.T, &ins.K, &ins.S, &ins.R, &ins.C1, &ins.Skip, &cv.Rule, &cv.T1, &cv.T2, &cv.C1, &cv.V}
	f := fields[r.Intn(len(fields))]
	*f = r.Intn(*f + 4)
}
