# zkLean — design

**Goal.** Given a public theorem statement `T` (written in a Lean-like
language against public definitions), produce a short proof π such that a
verifier is convinced that the prover knows a closed term `t` with `⊢ t : T`,
and learns nothing else about `t`.

```
public:  definitions, inductive declarations
         + statement T                        (examples/logic.public.lean)
private: proof term t                         (examples/logic.lean)
π:       196-byte Groth16 proof over BN254, ~2 ms to verify
```

## 1. Kernel

The trusted kernel is the Calculus of Constructions with Lean's universe
structure:

| construct | rule |
|---|---|
| `Sort u` | `Sort u : Sort (u+1)`; `Prop = Sort 0`, `Type = Sort 1` |
| `∀ x : A, B` | `A : Sort u`, `x:A ⊢ B : Sort v` ⇒ `Sort (imax u v)` (impredicative `Prop`) |
| `fun x : A => b` | standard; its type `∀ x:A, B` must itself be well-typed |
| `f a` | standard dependent application |
| `c.{u}` | `c` a constant of the public table: `c.{u} : Type(c)[BVar 0 := Sort u]` |
| conversion | `T ≡βι T'` and `T' : Sort s` ⇒ retype |

Representation is **locally nameless**: bound variables are de Bruijn
indices (`BVar`), free variables are de Bruijn *levels* (`FVar d` is the d-th
context entry). Every binder is opened by instantiating `BVar 0` with
`FVar(depth)`. Because the substituted term is always locally closed,
instantiation never needs index shifting, which keeps every substitution step
a constant-size local check.

Deliberately out of scope (see §6): universe polymorphism, mutual and nested
inductives, η, proof irrelevance, quotients, `δ`-unfolding (definitions are
expanded at elaboration — they are transparent macros, so the kernel only ever
sees β- and ι-redexes).

### Inductive types

An inductive declaration (`kernel/inductive.go`) is elaborated *publicly*.
The verifier re-runs the elaboration on the public file, so it trusts its own
copy of the result. Elaboration performs Lean's checks: the type former and
constructor types are well-typed; parameters are passed through unchanged;
recursive occurrences are strictly positive (`∀ ys, I ps is` with `I` absent
from `ys` and `is`); constructor fields live in a universe no larger than the
inductive's unless it is a `Prop`; and a `Prop` may eliminate into other
universes only if it is a syntactic subsingleton. Elaboration then produces
rows of the **constant table**: the former `I`, the constructors and
`I.rec`, each with its type.

There is no universe polymorphism, so the recursor's motive universe is a level
stored in the constant node itself (`I.rec.{u}`, tag `Const`, `B = u`). The
recursor's type is stored as a template whose `BVar 0` stands for `Sort u`.
Typing `I.rec.{u}` is a single instantiation row: `Type[BVar 0 := Sort u]`.
Recursors that only eliminate into `Prop` have a template without `BVar 0`.

Each constructor row also records its ι-rule as a closed right-hand side

```
Rhs_c = fun r ps motive minors fields => minor_c fields (fun ys => r ps motive minors ι'(ys) (f ys))…
rec a_1 … a_NRec (c b_1 … b_NCA)  ≡ι  Rhs_c rec a_1 … a_NPre b_{NCP+1} … b_NCA
```

The recursive call goes through the first argument `r`, which is
instantiated with the recursor itself, so `Rhs_c` does not depend on `u`.
The remaining β-steps are ordinary conversion rows. The outer λ-binders of
`Rhs_c` carry placeholder domains: they are always β-reduced immediately, and
conversion never looks at the domain of a redex. Only the `fun ys` binders
survive into reducts, so they carry the real field types. Untyped βι with
these rules is an orthogonal higher-order rewrite system, hence confluent, and
it is the same reduction Lean's kernel performs.

## 2. From type checking to a local relation

A type checker is recursive and data-dependent, which is a bad fit for a circuit.
The prover instead runs a *certifying* checker (`kernel/check.go`) that
records every step into flat tables. Each row can be checked by looking at
a constant number of other rows, and every reference points to a strictly
earlier row, so the derivation is well-founded by construction.

| table | row means | rules |
|---|---|---|
| terms | node `(tag, a, b)` + bounds `F, G` | children precede parents |
| ctx | `Γ' = Γ, x : A` (depth tracked) | parent precedes |
| lookup | `FVar l : A ∈ Γ` | base case or step to parent |
| inst | `t[BVar k := s] = r` | atom / bvar / skip / structural |
| consts (public) | constant `k` has type `Type[k]` (+ ι data for constructors) | — |
| iota walk | `U = rec a₁…aₙ`, `M = c b₁…bₘ`, `W = Rhs_c rec …` | rec base / rec arg / ctor base / ctor arg |
| conv | `t₁ ≡βι t₂` | refl, sym, trans, β, ι, Π/λ/app congruence |
| judgments | `Γ ⊢ t : T` | Sort, Var, Pi, Lam, App, Conv, Const |

**ι locally.** An ι-redex has two argument spines of unbounded length, so
the ι rule cannot be a single constant-size row. An *iota walk* consumes one
argument per row. It first walks the recursor's spine, with a counter `N`
and a bit `keep ⇔ N < NPre`, appending kept arguments to
`W = Rhs_c rec …`. It then walks the constructor's spine, starting only when
the recursor counter equals `NRec`, and appends `b_i` iff `i ≥ NCP`. A
`CIota` conversion row is valid when its walk has finished
(`N = NCA`): `App(U, M) ≡ W`. The `keep` bit is pinned both ways by two range
checks, so the prover cannot drop or add an argument. `NPre`, `NRec`, `NCP`,
`NCA`, the recursor index and `Rhs_c` come from the public constant table,
indexed by the walk's constructor.

`kernel/relation.go` is the native specification. `circuit/circuit.go`
implements the same checks line for line as R1CS.

**The two bounds.** Each term carries `F` (an upper bound on 1 + the highest
free-variable level) and `G` (an upper bound on 1 + the highest loose bound
index). The circuit only enforces that they are upper bounds, propagated
child→parent. That is enough for the three side conditions that make
locally-nameless sound:

* *local closedness*: `G = 0` for all judgment and conversion terms and for
  every substituted term, so instantiation-without-shifting is correct;
* *freshness*: in congruence under a binder the opening variable `x` satisfies
  `x ≥ F(B₁), F(B₂)`; in typing, `F(subject), F(type) ≤ depth(Γ)`, so
  `FVar(depth)` is fresh;
* *skip*: `G(t) ≤ k` ⇒ `BVar k` does not occur ⇒ `t[k := s] = t`. One range
  check replaces a whole subtree of instantiation rows (this halved
  instantiation rows on the examples).

**Root.** The last judgment row must be `∅ ⊢ t : T` with `T` = the public
statement id and `F(t) = G(t) = 0` (closed).

### Soundness sketch
By induction on row index (references go backwards): every inst row whose
input satisfies the closedness invariant computes real substitution; every
iota-walk row describes real spines (by induction on `Prev`, each step adds
exactly one argument, and `keep` is pinned by range checks), so every conv row
reachable from a judgment derives a real βι-equation (rules are the
equivalence-congruence closure of one-step β and ι, with fresh opening); every
judgment row reachable from the root is an instance of a rule of λC extended
with the public constants, in a well-formed context. Contexts are well-formed because the only rules that
extend a context (Pi, Lam) type-check the new hypothesis in the same row. Junk
rows the prover adds are harmless: they are never reachable from the root, or
they are valid derivations themselves. So a satisfying witness yields a closed
derivation `⊢ t : T`. λC with this universe hierarchy, extended with
inductive families that pass the positivity, universe and elimination checks
(the fragment of the Calculus of Inductive Constructions that Lean's kernel
implements, without mutual or nested types), is strongly normalising and
consistent, so for example `False` has no witness.

## 3. Circuit

* **Memory:** each table column is a gnark `logderivlookup` table; a reference
  `row[j].field` costs O(1) constraints (log-derivative argument, challenge
  derived via the Groth16 BSB22 commitment).
* **Order and inequalities:** `a < b` ⇔ `b − a − 1 ∈ [0, 2¹⁶)` via gnark's
  commitment-based range checker. Every integer-valued field is range-checked,
  so field and integer semantics coincide.
* **Rule dispatch:** a one-hot selector per row; each rule's constraints are
  multiplied by its selector.
* **Public inputs:** the constant table, plus the term DAG of its types,
  ι right-hand sides and the statement, laid out canonically in rows
  `0..NP-1` (`kernel.PublicLayout`), plus the statement's root id. The
  verifier rebuilds these from the public source file, so no hash gadget is
  needed. Unused constant rows have type `Prop`: at worst they act as opaque
  propositional atoms, which is a conservative extension.

| profile | NT/NI/NC/NJ rows | constraints | setup | prove | proof | verify |
|---|---|---|---|---|---|---|
| small | 768/512/128/192 | 211,331 | 26 s | 1.6 s | 196 B | ~3 ms |
| default | 1280/1024/320/640 | 470,478 | 46 s | 2.4 s | 196 B | ~5 ms |
| large | 4096/4096/1024/2048 | 1,554,255 | 158 s | 7.5 s | 196 B | ~3–5 ms |

Measured on an 8-core machine. The public-input count is now 1,026 (small),
1,666 (default) and 2,050 (large), because the constant table is public. This accounts for
most of the increase in verification time. Hashing the public inputs into
one commitment would remove it.

## 4. Zero knowledge — what leaks
Groth16 is perfectly zero-knowledge. gnark masks each in-circuit commitment
with a random value, so the lookup and range-check commitments hide the
witness too (this was not true before gnark v0.11, CVE-2024-45040; this project
uses v0.16.5). Revealed: the statement, the definitions and inductive declarations of the public file, the capacity
profile (an upper bound on the derivation's size), and that a proof exists.
Not revealed: the proof term, its size below capacity, which lemmas or tactics
produced it, and the derivation's shape. Timing side channels of the prover
are out of scope.

## 5. Testing
* `kernel`: every example certifies; invalid proofs are rejected (wrong
  argument order, `False`, `Type : Type`, `1+1 = 1`); public statements laid
  out from the stripped file match the private file byte for byte.
* **Relation fuzzing:** 3,000 random corruptions of a valid certificate. ~20%
  still satisfy the relation (they hit unused fields or padding). For every one
  of those, the root term is re-checked by the independent reference checker.
  No unsound acceptance has been found.
* inductives: proofs that need ι-reduction, large elimination and induction
  certify, including indexed families (`Vec`) and function-typed recursive
  fields. Ill-formed declarations are rejected: negative and non-strictly
  positive occurrences, oversized fields, changed parameters, `I` in an
  index, and large elimination of a non-subsingleton `Prop`. A second
  relation fuzzer targets the iota-walk rows of a certificate.
* `circuit`: honest witnesses solve; six targeted forgeries are rejected by both
  the relation and the circuit (wrong statement, cyclic self-justification,
  variable outside its context, bogus β-step, `Type : Type`, non-fresh
  congruence variable), plus six against inductives (bogus ι result, ι on an
  unfinished walk, a dropped argument, a switched constructor, a constant at
  the wrong type, a recursor at the wrong universe). A refinement fuzz test confirms that the circuit never
  accepts what the relation rejects.
* CLI: replaying a proof against another theorem, tampering with a public
  definition, and bit-flipping the proof are all rejected.

## 6. Limitations and roadmap
1. **Trusted setup.** `zklean setup` is single-party: whoever runs it can
   forge proofs. Production use needs gnark's Groth16 MPC ceremony
   (`backend/groth16/bn254/mpcsetup`) or a PLONK/KZG backend with a universal
   SRS (the circuit uses no Groth16-specific features).
2. **Fixed capacity.** Proofs above the profile size need a bigger circuit.
   The scalable route is folding (Nova/HyperNova-style IVC over a
   *per-row* step circuit). The tables are already row-local, so this is a
   natural fit.
3. **Kernel coverage.** Reaching real Lean needs:
   (a) ~~inductive types~~ (done, §1); still missing are mutual and nested
   inductives, structure η and proof irrelevance;
   (b) universe polymorphism (would subsume the `.{u}` recursor levels): a level-expression table with `max/imax/succ`
   normalisation rows;
   (c) δ-reduction with a public definition table instead of macro expansion,
   to avoid exponential statement blow-up;
   (d) an importer for `lean4export` output.
   With (a)–(d), any Mathlib theorem could get a ZK proof of provability. The
   alternative — running an existing Lean checker (e.g. lean4lean, nanoda) in
   a zkVM like RISC Zero or SP1 — gets full coverage sooner but costs about
   10⁹–10¹⁰ cycles for non-trivial proofs.
4. **Normalisation strategy.** The prover decides conversion by full
   β-normalisation. Lazy whnf with sharing would shrink certificates a lot.
   Only the prover changes; the relation is unaffected.
