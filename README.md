# zkLean

Zero-knowledge proofs of theoremhood for a Lean-style dependent type theory.

You write theorems and proofs in a Lean subset. zkLean produces a 196-byte
Groth16 proof that you hold a valid proof of the stated theorem. A verifier
checks it in about 2 ms, without ever seeing your proof.

```
$ go build -o bin/zklean ./cmd/zklean
$ ./bin/zklean check examples/logic.lean                 # ordinary type checking
$ ./bin/zklean statement examples/logic.lean > pub.lean  # strip proofs → `sorry`
$ ./bin/zklean setup                                     # one-off, ~75 s (default profile)
$ ./bin/zklean prove examples/logic.lean two_plus_two    # ~5 s → two_plus_two.zkp
$ ./bin/zklean verify pub.lean two_plus_two.zkp
✓ VALID [2.1ms]: the prover knows a closed proof term of
  theorem two_plus_two : Eq Nat (add two two) four
```

Use `-profile small` for a ~2× faster setup and prove, with lower capacity.

## Language

```lean
def And (A B : Prop) : Prop := ∀ (C : Prop), (A → B → C) → C

theorem and_comm : ∀ (A B : Prop), And A B → And B A :=
  fun (A B : Prop) (h : And A B) (C : Prop) (k : B → A → C) =>
    h C (fun (a : A) (b : B) => k b a)
```

The kernel is the Calculus of Constructions with `Prop : Type : Type 1 : …` (Lean's
universe structure, impredicative `Prop`, `imax`) and β-conversion. There are no
inductive types, no universe polymorphism, no tactics, and binder types are required.
Definitions are public and transparent; theorem bodies are private.

## Layout

| path | contents |
|---|---|
| `kernel/term.go` | hash-consed locally-nameless term DAG |
| `kernel/parse.go` | parser and elaborator; public-statement extraction |
| `kernel/check.go` | certifying type checker; emits the flat certificate |
| `kernel/relation.go` | native specification of the ZK relation |
| `circuit/circuit.go` | the same relation as an R1CS (gnark, BN254) |
| `cmd/zklean` | CLI |
| `DESIGN.md` | design, soundness sketch, costs, limitations |

`go test ./...` runs the kernel tests, the soundness fuzzers and the forgery
tests (about 20 s).

⚠️ `zklean setup` is a single-party trusted setup: whoever runs it can forge
proofs. It is fine for experiments, not for adversarial use. See DESIGN.md §6.
