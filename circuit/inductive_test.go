package circuit

import (
	"fmt"
	"math/rand"
	"os"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/test"
	"github.com/river/zklean/kernel"
)

func certInd(t *testing.T, name string, sz kernel.Sizes) *kernel.Certificate {
	src, err := os.ReadFile("../examples/inductive.lean")
	if err != nil {
		t.Fatal(err)
	}
	env, err := kernel.Parse(string(src))
	if err != nil {
		t.Fatal(err)
	}
	d, _ := env.Lookup(name)
	c, err := kernel.Certify(env.S, d.Type, d.Value, sz)
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

// A proof that needs large elimination and ι-reduction solves the circuit.
func TestHonestWitnessInductive(t *testing.T) {
	for _, name := range []string{"true_ne_false", "and_swap"} {
		c := certInd(t, name, tiny)
		if err := test.IsSolved(New(tiny), Assign(c, tiny), ecc.BN254.ScalarField()); err != nil {
			t.Fatalf("%s: %v", name, err)
		}
	}
}

func TestForgedInductiveWitnesses(t *testing.T) {
	iotaConv := func(c *kernel.Certificate) *kernel.ConvRow {
		for i := range c.Conv {
			if c.Conv[i].Rule == kernel.CIota {
				return &c.Conv[i]
			}
		}
		panic("no iota row")
	}
	forges := []struct {
		name string
		f    func(c *kernel.Certificate)
	}{
		{"bogus iota result", func(c *kernel.Certificate) {
			r := iotaConv(c)
			r.T2 = r.T1
		}},
		{"iota on an unfinished walk", func(c *kernel.Certificate) {
			r := iotaConv(c)
			r.I1--
		}},
		{"iota walk drops a kept argument", func(c *kernel.Certificate) {
			for i := range c.Iota {
				w := &c.Iota[i]
				if w.Kind == kernel.WRecArg && w.Keep == 1 {
					w.Keep, w.W = 0, c.Iota[w.Prev].W
					return
				}
			}
			panic("no kept argument")
		}},
		{"iota walk switches constructor", func(c *kernel.Certificate) {
			for i := range c.Iota {
				if c.Iota[i].Kind == kernel.WCtorBase {
					c.Iota[i].Ctor++
					return
				}
			}
		}},
		{"constant with the wrong type", func(c *kernel.Certificate) {
			for i := range c.Jud {
				if c.Jud[i].Rule == kernel.JConst {
					c.Jud[i].Ty = 0
					return
				}
			}
		}},
		{"recursor at a different universe than its type", func(c *kernel.Certificate) {
			for i := range c.Jud {
				r := &c.Jud[i]
				if r.Rule == kernel.JConst && c.S.N(r.Subj).B > 0 {
					r.V = c.S.Sort(c.S.N(r.Subj).B + 1)
					return
				}
			}
			panic("no large recursor")
		}},
	}
	for _, fg := range forges {
		c := certInd(t, "true_ne_false", tiny)
		fg.f(c)
		if c.Relation(tiny) == nil {
			t.Fatalf("%s: native relation accepted forgery", fg.name)
		}
		var err error
		func() {
			defer func() {
				if r := recover(); r != nil {
					err = fmt.Errorf("panic: %v", r)
				}
			}()
			err = test.IsSolved(New(tiny), Assign(c, tiny), ecc.BN254.ScalarField())
		}()
		if err == nil {
			t.Fatalf("%s: circuit accepted forgery", fg.name)
		}
		t.Logf("rejected: %s", fg.name)
	}
}

// The circuit never accepts an ι/constant witness that the relation rejects.
func TestCircuitRefinesRelationInductive(t *testing.T) {
	rng := rand.New(rand.NewSource(11))
	for trial := 0; trial < 30; trial++ {
		c := certInd(t, "true_ne_false", tiny)
		used := 0
		for used < len(c.Iota) && c.Iota[used].Kind != kernel.WPad {
			used++
		}
		switch rng.Intn(3) {
		case 0:
			w := &c.Iota[rng.Intn(used)]
			f := []*int{&w.Kind, &w.Ctor, &w.U, &w.M, &w.W, &w.N, &w.Prev, &w.Keep}
			*f[rng.Intn(len(f))] += rng.Intn(5) - 2
		case 1:
			for i := range c.Conv {
				if c.Conv[i].Rule == kernel.CIota && rng.Intn(2) == 0 {
					f := []*int{&c.Conv[i].T1, &c.Conv[i].T2, &c.Conv[i].I1}
					*f[rng.Intn(len(f))] += rng.Intn(5) - 2
					break
				}
			}
		case 2:
			for i := range c.Jud {
				if c.Jud[i].Rule == kernel.JConst && rng.Intn(3) == 0 {
					f := []*int{&c.Jud[i].Subj, &c.Jud[i].Ty, &c.Jud[i].V, &c.Jud[i].I1}
					*f[rng.Intn(len(f))] += rng.Intn(5) - 2
					break
				}
			}
		}
		native := c.Relation(tiny) == nil
		inCircuit := false
		func() {
			defer func() { recover() }()
			inCircuit = test.IsSolved(New(tiny), Assign(c, tiny), ecc.BN254.ScalarField()) == nil
		}()
		if inCircuit && !native {
			t.Fatalf("trial %d: circuit accepted a witness the relation rejects", trial)
		}
	}
}
