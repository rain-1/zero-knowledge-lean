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

## How inductive types work in zero knowledge

A zk-SNARK circuit has a fixed shape, but a type checker recurses, branches and
normalises for as long as it needs. zkLean bridges this gap by having the prover
run a *certifying* checker. The checker writes every step of the typing
derivation as a row in a few flat tables, and each row can be checked by
looking at a constant number of earlier rows. The circuit only checks these
rows; it never searches. Inductive types had to fit that pattern. They put
pressure on it in three places: checking a declaration (positivity, universes,
which elimination is allowed), typing `Nat.rec` without universe polymorphism,
and ι-reduction, whose redex has two argument lists of unbounded length. Four
ideas made it work.

**1. Declarations are public, so they are checked outside the circuit.** A
theorem about `Nat` is meaningless unless the verifier knows what `Nat` is, so
inductive declarations are part of the public statement. The verifier
elaborates them itself (`kernel/inductive.go`) with Lean's checks:
well-typedness, parameters passed through unchanged, strict positivity, field
universes, and large elimination from `Prop` only for subsingletons.
Elaboration produces a **constant table** holding each constant's type and
each constructor's ι-rule. The table is a public input of the circuit, built
deterministically by both prover and verifier from the same public text. All
the hard, non-local analysis runs natively, on public data. The circuit only
*uses* the table. Editing a declaration, even reordering `Bool`'s constructors,
changes the public inputs and invalidates the proof.

**2. Constants are table lookups, and a recursor's universe is a
substitution.** A constant is a new leaf `Const(k, u)` in the term DAG, and
typing it is one judgment row plus one row of the existing substitution table:
`c.{u} : Type(c)[BVar 0 := Sort u]`. The kernel has no universe polymorphism,
so a recursor's type is stored as a template in which `BVar 0` stands for the
motive's universe `Sort u`, and the level is written in the source:
`Nat.rec.{0}` to prove by induction, `Nat.rec.{1}` to compute into `Type`.

**3. Each ι-rule is one closed term.** Instead of pattern matching in the
circuit, each constructor stores a closed right-hand side in which the
recursor is an argument `r`:

```
Rhs_succ = fun r P z s n => s n (r P z s n)
Nat.rec P z s (Nat.succ n)  ≡ι  Rhs_succ Nat.rec P z s n   -- then plain β-steps
```

The remaining β-reductions use rows the circuit already checks. Passing the
recursor in as `r` keeps one public `Rhs` valid at every universe level. As in
Lean's kernel, the rule ignores the constructor's copy of the parameters and
the recursor's indices. Untyped β plus these rules is an orthogonal rewrite
system, so it is confluent.

**4. Argument lists are walked one row at a time.** An ι-step relates
`U = rec a₁ … a_NRec`, `M = c b₁ … b_NCA` and
`W = Rhs_c rec a₁ … a_NPre b_{NCP+1} … b_NCA`. `W` keeps the parameters,
motive and minor premises but drops the indices, and keeps the constructor's
fields but drops its parameters. Both lists can be any length, so a new
**iota-walk table** builds `U`, `M` and `W` together, one argument per row.
Each row is either a base (`U = rec` or `M = c`) or a step that extends the
previous row by one argument. A `keep` bit decides whether the argument is
also appended to `W`. Range checks pin `keep` in both directions
(`keep ⇔ N < NPre` for the recursor's arguments, `keep ⇔ N ≥ NCP` for the
constructor's), so the prover cannot drop or insert an argument. A conversion
row then points at a finished walk and concludes `App(U, M) ≡ W`. For
`Nat.rec P z s (Nat.succ k)` the walk has six rows:

| # | kind | U | M | W |
|---|---|---|---|---|
| 0 | rec base | `rec` | | `Rhs rec` |
| 1–3 | rec args (kept) | `rec P`, `rec P z`, `rec P z s` | | `Rhs rec P`, …, `Rhs rec P z s` |
| 4 | ctor base | `rec P z s` | `succ` | `Rhs rec P z s` |
| 5 | ctor arg (kept) | `rec P z s` | `succ k` | `Rhs rec P z s k` |

**Soundness.** The argument is by induction on row index, since every reference
points backwards. Every walk describes real argument lists, so every ι-row is
a genuine instance of the declaration's ι-rule. Every judgment row is then an
instance of a typing rule of the Calculus of Constructions extended with the
public constants. Because the declarations passed Lean's checks, this is the
fragment of the Calculus of Inductive Constructions that Lean's kernel
implements, without mutual or nested types, which is consistent. The native
relation (`kernel/relation.go`) and the circuit (`circuit/circuit.go`) are
written in lockstep. Tests check three things: the circuit never accepts what
the relation rejects; targeted forgeries are rejected (a bogus ι result, an
unfinished walk, a dropped argument, a switched constructor, a constant at the
wrong type, a recursor at the wrong universe); and randomly corrupted
certificates either fail or still encode a valid proof.

**Cost.** Proofs are still 196 bytes and verify in a few milliseconds. The
public constant table raised the public-input count to between 1,026 and 2,050,
depending on the profile. The default circuit grew from 396k to 470k
constraints. Induction proofs such as `add_comm` produce large certificates
because the prover normalises terms fully, hence the opt-in `large` profile.
Lazy weak-head reduction in the prover would shrink them without changing the
circuit. See `DESIGN.md` for the full design.

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
