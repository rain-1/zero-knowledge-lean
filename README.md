# zkLean

<img width="2105" height="1257" alt="image" src="https://github.com/user-attachments/assets/5407600f-1bba-41ae-b54b-ee5e7a22dd7b" />


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

Use `-profile small` for a ~2× faster setup and prove, with lower capacity, or
`-profile large` for longer proofs such as the induction proofs below.

## Examples

Each file has a matching `*.public.lean`, the statement-only version a verifier sees.

| file | contents |
|---|---|
| `examples/logic.lean` | Church-encoded logic and arithmetic (no inductives) |
| `examples/inductive.lean` | a tour: `And`/`Or`/`Eq`/`Nat`/`Exists`, ι, large elimination, induction |
| `examples/nat.lean` | `add`/`mul`/`pred`, `Eq` symm/trans/congr, `succ_ne_zero`, `succ_inj`, `add_assoc`, `add_comm` |
| `examples/list.lean` | polymorphic `List`: `append`, `map`, `length`, `append_nil`, `length_append`, `length_map` |
| `examples/data.lean` | `Bool`, `Option`, `Prod`, `Sum`, `Sigma`; `not_not`, `swap_swap`, `Prod` η by induction |
| `examples/predicates.lean` | inductive predicates `Le` and `Even`: `le_trans`, `even_double`, `¬ Even 1` by inversion |

`zklean check FILE` reports, for each theorem, whether it fits the default
profile. Use `-profile large` to see which theorems need it: `add_comm`,
`length_append`, `swap_swap` and the other induction proofs over lists and
pairs.

## Language

```lean
def And (A B : Prop) : Prop := ∀ (C : Prop), (A → B → C) → C

theorem and_comm : ∀ (A B : Prop), And A B → And B A :=
  fun (A B : Prop) (h : And A B) (C : Prop) (k : B → A → C) =>
    h C (fun (a : A) (b : B) => k b a)
```

Inductive families work as in Lean, with recursors and ι-reduction:

```lean
inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

inductive Eq (A : Type) (a : A) : A → Prop where
  | refl : Eq A a a

def add (m n : Nat) : Nat :=
  Nat.rec.{1} (fun (_ : Nat) => Nat) m (fun (k : Nat) (ih : Nat) => Nat.succ ih) n

theorem two_plus_two : Eq Nat (add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ (Nat.succ Nat.zero)))
    (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) :=
  Eq.refl Nat (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
```

Each declaration adds `I`, `I.ctor…` and `I.rec`. All arguments are explicit,
including parameters and the motive. Because there is no universe polymorphism,
a recursor that can eliminate into any universe takes its universe as a level:
`Nat.rec.{0}` for proofs by induction, `Nat.rec.{1}` to compute into `Type`.
Declarations are checked the way Lean checks them: strict positivity, field
universes, and large elimination from `Prop` only for subsingletons. Mutual and
nested inductives are not supported. See `examples/inductive.lean` for
induction, `true ≠ false` (large elimination) and `Exists`.

The kernel is the Calculus of Constructions with `Prop : Type : Type 1 : …` (Lean's
universe structure, impredicative `Prop`, `imax`), these inductive types, and
βι-conversion. There is no universe polymorphism, no tactics, and binder types are
required. Definitions and inductive declarations are public; definitions are
transparent; theorem bodies are private.

## Layout

| path | contents |
|---|---|
| `kernel/term.go` | hash-consed locally-nameless term DAG |
| `kernel/parse.go` | parser and elaborator; public-statement extraction |
| `kernel/inductive.go` | inductive declarations: checks, recursors, ι-rules |
| `kernel/check.go` | certifying type checker; emits the flat certificate |
| `kernel/relation.go` | native specification of the ZK relation |
| `circuit/circuit.go` | the same relation as an R1CS (gnark, BN254) |
| `cmd/zklean` | CLI |
| `DESIGN.md` | design, soundness sketch, costs, limitations |

`go test ./...` runs the kernel tests, the soundness fuzzers and the forgery
tests (about a minute).

⚠️ `zklean setup` is a single-party trusted setup: whoever runs it can forge
proofs. It is fine for experiments, not for adversarial use. See DESIGN.md §6.
