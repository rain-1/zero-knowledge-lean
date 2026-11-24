// Command zklean: zero-knowledge proofs of theoremhood for a Lean-style kernel.
//
//	zklean check     FILE                    type-check every declaration
//	zklean statement FILE                    print FILE with all proofs replaced by `sorry`
//	zklean setup     [-profile p]            compile circuit + Groth16 setup
//	zklean prove     [-profile p] FILE THM   produce THM.zkp (reveals nothing about the proof)
//	zklean verify    PUBLIC_FILE PROOF.zkp   check a proof against the public statement
package main

import (
	"bytes"
	"encoding/base64"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/logger"
	"github.com/rs/zerolog"

	"github.com/river/zklean/circuit"
	"github.com/river/zklean/kernel"
)

type proofFile struct {
	Format  string       `json:"format"`
	Profile string       `json:"profile"`
	Sizes   kernel.Sizes `json:"sizes"`
	Theorem string       `json:"theorem"`
	Proof   string       `json:"groth16_proof"`
}

func die(f string, a ...any) {
	fmt.Fprintf(os.Stderr, "zklean: "+f+"\n", a...)
	os.Exit(1)
}

func usage() {
	fmt.Fprintln(os.Stderr, `usage:
  zklean check     FILE
  zklean statement FILE
  zklean setup     [-profile small|default|large] [-keys DIR]
  zklean prove     [-profile small|default|large] [-keys DIR] [-o OUT] FILE THEOREM
  zklean verify    [-keys DIR] PUBLIC_FILE PROOF.zkp`)
	os.Exit(2)
}

func main() {
	logger.Set(zerolog.Nop())
	if len(os.Args) < 2 {
		usage()
	}
	cmd := os.Args[1]
	fs := flag.NewFlagSet(cmd, flag.ExitOnError)
	profile := fs.String("profile", "default", "circuit capacity profile (small|default|large)")
	keys := fs.String("keys", "keys", "directory holding circuit, proving and verifying keys")
	out := fs.String("o", "", "output proof file (default THEOREM.zkp)")
	// allow flags before and after positional arguments
	var args []string
	rest := os.Args[2:]
	for {
		fs.Parse(rest)
		rest = fs.Args()
		if len(rest) == 0 {
			break
		}
		args = append(args, rest[0])
		rest = rest[1:]
	}
	switch cmd {
	case "check":
		if len(args) != 1 {
			usage()
		}
		cmdCheck(args[0], *profile)
	case "statement":
		if len(args) != 1 {
			usage()
		}
		fmt.Print(load(args[0]).PublicSource())
	case "setup":
		cmdSetup(*profile, *keys)
	case "prove":
		if len(args) != 2 {
			usage()
		}
		o := *out
		if o == "" {
			o = args[1] + ".zkp"
		}
		cmdProve(*profile, *keys, args[0], args[1], o)
	case "verify":
		if len(args) != 2 {
			usage()
		}
		cmdVerify(*keys, args[0], args[1])
	default:
		usage()
	}
}

func load(path string) *kernel.Env {
	src, err := os.ReadFile(path)
	if err != nil {
		die("%v", err)
	}
	env, err := kernel.Parse(string(src))
	if err != nil {
		die("%s: %v", path, err)
	}
	return env
}

func sizes(profile string) kernel.Sizes {
	sz, ok := kernel.Profiles[profile]
	if !ok {
		die("unknown profile %q", profile)
	}
	return sz
}

func cmdCheck(path, profile string) {
	env := load(path)
	sz := sizes(profile)
	ok := true
	for _, d := range env.Decls {
		ts, ty, err := kernel.TypeOf(env.S, d.Type)
		if err == nil && ts.N(ty).Tag != kernel.TSort {
			err = fmt.Errorf("statement is not a type")
		}
		if err != nil {
			fmt.Printf("✗ %s %s: ill-formed statement: %v\n", d.Kind, d.Name, err)
			ok = false
			continue
		}
		if d.Kind == "inductive" {
			fmt.Printf("✓ inductive %s  [%s]\n", d.Name, strings.Join(env.Constants(d.Name), ", "))
			continue
		}
		if d.Value < 0 {
			fmt.Printf("· %s %s : sorry\n", d.Kind, d.Name)
			continue
		}
		c, err := kernel.Certify(env.S, d.Type, d.Value, sz)
		if err != nil {
			fmt.Printf("✗ %s %s: %v\n", d.Kind, d.Name, err)
			ok = false
			continue
		}
		u := c.Usage()
		fit := "fits " + profile
		if err := c.Pad(sz); err != nil {
			fit = "exceeds " + profile + " capacity"
		}
		fmt.Printf("✓ %s %s  [judgments %d, conv %d, inst %d; %s]\n", d.Kind, d.Name, u["judgments"], u["conv"], u["inst"], fit)
	}
	if !ok {
		os.Exit(1)
	}
}

func keyPath(dir, profile, ext string) string { return filepath.Join(dir, profile+"."+ext) }

func cmdSetup(profile, dir string) {
	sz := sizes(profile)
	t0 := time.Now()
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit.New(sz))
	if err != nil {
		die("compile: %v", err)
	}
	fmt.Printf("compiled circuit (%s): %d constraints, %d public inputs [%v]\n",
		profile, ccs.GetNbConstraints(), ccs.GetNbPublicVariables(), time.Since(t0).Round(time.Millisecond))
	t0 = time.Now()
	// NOTE: single-party setup. Whoever runs this knows the toxic waste and
	// could forge proofs; production use needs an MPC ceremony (gnark's
	// backend/groth16/bn254/mpcsetup) or a universal-SRS backend.
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		die("setup: %v", err)
	}
	fmt.Printf("groth16 setup done [%v]\n", time.Since(t0).Round(time.Millisecond))
	os.MkdirAll(dir, 0o755)
	save := func(path string, f func(*os.File) error) {
		fh, err := os.Create(path)
		if err != nil {
			die("%v", err)
		}
		defer fh.Close()
		if err := f(fh); err != nil {
			die("write %s: %v", path, err)
		}
	}
	save(keyPath(dir, profile, "ccs"), func(f *os.File) error { _, err := ccs.WriteTo(f); return err })
	save(keyPath(dir, profile, "pk"), func(f *os.File) error { _, err := pk.WriteRawTo(f); return err })
	save(keyPath(dir, profile, "vk"), func(f *os.File) error { _, err := vk.WriteTo(f); return err })
	fmt.Printf("wrote %s.{ccs,pk,vk} to %s/\n", profile, dir)
}

func readKeys(dir, profile string, needProver bool) (constraint.ConstraintSystem, groth16.ProvingKey, groth16.VerifyingKey) {
	open := func(ext string) *os.File {
		f, err := os.Open(keyPath(dir, profile, ext))
		if err != nil {
			die("%v (run `zklean setup -profile %s` first)", err, profile)
		}
		return f
	}
	vk := groth16.NewVerifyingKey(ecc.BN254)
	f := open("vk")
	if _, err := vk.ReadFrom(f); err != nil {
		die("read vk: %v", err)
	}
	f.Close()
	if !needProver {
		return nil, nil, vk
	}
	ccs := groth16.NewCS(ecc.BN254)
	f = open("ccs")
	if _, err := ccs.ReadFrom(f); err != nil {
		die("read ccs: %v", err)
	}
	f.Close()
	pk := groth16.NewProvingKey(ecc.BN254)
	f = open("pk")
	if _, err := pk.UnsafeReadFrom(f); err != nil {
		die("read pk: %v", err)
	}
	f.Close()
	return ccs, pk, vk
}

func cmdProve(profile, dir, path, thm, out string) {
	sz := sizes(profile)
	env := load(path)
	d, ok := env.Lookup(thm)
	if !ok || d.Kind != "theorem" {
		die("no theorem %q in %s", thm, path)
	}
	if d.Value < 0 {
		die("%s has no proof (sorry)", thm)
	}
	t0 := time.Now()
	cert, err := kernel.Certify(env.S, d.Type, d.Value, sz)
	if err != nil {
		die("%s does not type-check:\n%v", thm, err)
	}
	if err := cert.Pad(sz); err != nil {
		die("%v", err)
	}
	if err := cert.Relation(sz); err != nil {
		die("internal error: certificate violates relation: %v", err)
	}
	fmt.Printf("kernel accepted %s; certificate built [%v]\n", thm, time.Since(t0).Round(time.Millisecond))
	ccs, pk, vk := readKeys(dir, profile, true)
	w, err := frontend.NewWitness(circuit.Assign(cert, sz), ecc.BN254.ScalarField())
	if err != nil {
		die("witness: %v", err)
	}
	t0 = time.Now()
	proof, err := groth16.Prove(ccs, pk, w)
	if err != nil {
		die("prove: %v", err)
	}
	fmt.Printf("groth16 proof generated [%v]\n", time.Since(t0).Round(time.Millisecond))
	pub, _ := w.Public()
	if err := groth16.Verify(proof, vk, pub); err != nil {
		die("self-check failed: %v", err)
	}
	var buf bytes.Buffer
	proof.WriteTo(&buf)
	pf := proofFile{Format: "zklean-groth16-bn254-v2", Profile: profile, Sizes: sz, Theorem: thm,
		Proof: base64.StdEncoding.EncodeToString(buf.Bytes())}
	js, _ := json.MarshalIndent(pf, "", "  ")
	if err := os.WriteFile(out, append(js, '\n'), 0o644); err != nil {
		die("%v", err)
	}
	fmt.Printf("wrote %s (%d-byte proof)\n", out, buf.Len())
}

func cmdVerify(dir, pubPath, proofPath string) {
	raw, err := os.ReadFile(proofPath)
	if err != nil {
		die("%v", err)
	}
	var pf proofFile
	if err := json.Unmarshal(raw, &pf); err != nil || pf.Format != "zklean-groth16-bn254-v2" {
		die("%s: not a zklean proof", proofPath)
	}
	sz := sizes(pf.Profile)
	if sz != pf.Sizes {
		die("proof was made for different circuit sizes")
	}
	env := load(pubPath)
	d, ok := env.Lookup(pf.Theorem)
	if !ok || d.Kind != "theorem" {
		die("public file has no theorem %q", pf.Theorem)
	}
	s, root, err := kernel.PublicLayout(env.S, d.Type, sz, map[int]int{})
	if err != nil {
		die("%v", err)
	}
	assign := circuit.New(sz)
	circuit.PublicAssign(assign, s, root, sz)
	pub, err := frontend.NewWitness(assign, ecc.BN254.ScalarField(), frontend.PublicOnly())
	if err != nil {
		die("public witness: %v", err)
	}
	pbytes, err := base64.StdEncoding.DecodeString(pf.Proof)
	if err != nil {
		die("bad proof encoding")
	}
	proof := groth16.NewProof(ecc.BN254)
	if _, err := proof.ReadFrom(bytes.NewReader(pbytes)); err != nil {
		die("bad proof: %v", err)
	}
	_, _, vk := readKeys(dir, pf.Profile, false)
	t0 := time.Now()
	if err := groth16.Verify(proof, vk, pub); err != nil {
		fmt.Printf("✗ INVALID proof for %s\n", pf.Theorem)
		os.Exit(1)
	}
	fmt.Printf("✓ VALID [%v]: the prover knows a closed proof term of\n  theorem %s %s\n  (fully elaborated statement: %d DAG nodes, unfolding definitions from %s)\n",
		time.Since(t0).Round(time.Microsecond), pf.Theorem, d.Signature, s.Size(root), pubPath)
}
