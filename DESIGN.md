# zkLean — design

**Goal.** Given a public theorem statement `T` (written in a Lean-like
language against public definitions), produce a short proof π such that a
verifier is convinced that the prover knows a closed term `t` with `⊢ t : T`,
and learns nothing else about `t`.

```
public:  definitions + statement T            (examples/logic.public.lean)
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
| conversion | `T ≡β T'` and `T' : Sort s` ⇒ retype |

Representation is **locally nameless**: bound variables are de Bruijn
indices (`BVar`), free variables are de Bruijn *levels* (`FVar d` is the d-th
context entry). Every binder is opened by instantiating `BVar 0` with
`FVar(depth)`. Because the substituted term is always locally closed,
instantiation never needs index shifting, which keeps every substitution step
a constant-size local check.

Deliberately out of scope (see §6): inductive types and recursors,
universe polymorphism, η, proof irrelevance, quotients, `δ`-unfolding
(definitions are expanded at elaboration — they are transparent macros, so the
kernel only ever sees β-redexes).

## 2. From type checking to a local relation

A type checker is recursive and data-dependent, which is a bad fit for a circuit.
The prover instead runs a *certifying* checker (`kernel/check.go`) that
records every step into six flat tables. Each row can be checked by looking at
a constant number of other rows, and every reference points to a strictly
earlier row, so the derivation is well-founded by construction.

| table | row means | rules |
|---|---|---|
| terms | node `(tag, a, b)` + bounds `F, G` | children precede parents |
| ctx | `Γ' = Γ, x : A` (depth tracked) | parent precedes |
| lookup | `FVar l : A ∈ Γ` | base case or step to parent |
| inst | `t[BVar k := s] = r` | atom / bvar / skip / structural |
| conv | `t₁ ≡β t₂` | refl, sym, trans, β, Π/λ/app congruence |
| judgments | `Γ ⊢ t : T` | Sort, Var, Pi, Lam, App, Conv |

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
conv row reachable from a judgment derives a real β-equation (rules are the
equivalence-congruence closure of one-step β, with fresh opening); every
judgment row reachable from the root is an instance of a λC rule in a
well-formed context. Contexts are well-formed because the only rules that
extend a context (Pi, Lam) type-check the new hypothesis in the same row. Junk
rows the prover adds are harmless: they are never reachable from the root, or
they are valid derivations themselves. So a satisfying witness yields a closed
derivation `⊢ t : T`. λC with this universe hierarchy is strongly normalising
and consistent, so for example `∀ C : Prop, C` has no witness.

## 3. Circuit

* **Memory:** each table column is a gnark `logderivlookup` table; a reference
  `row[j].field` costs O(1) constraints (log-derivative argument, challenge
  derived via the Groth16 BSB22 commitment).
* **Order and inequalities:** `a < b` ⇔ `b − a − 1 ∈ [0, 2¹⁶)` via gnark's
  commitment-based range checker. Every integer-valued field is range-checked,
  so field and integer semantics coincide.
* **Rule dispatch:** a one-hot selector per row; each rule's constraints are
  multiplied by its selector.
* **Public inputs:** the statement's DAG laid out canonically in rows
  `0..NP-1` (`kernel.PublicLayout`), plus its root id. The verifier rebuilds
  these from the public source file, so no hash gadget is needed.

| profile | NT/NI/NC/NJ rows | constraints | setup | prove | proof | verify |
|---|---|---|---|---|---|---|
| small | 512/512/128/192 | 165,834 | 32 s | 2.2 s | 196 B | ~2 ms |
| default | 1024/1024/320/640 | 396,489 | 73 s | 4.8 s | 196 B | ~2.5 ms |

Measured on a 2-core cloud VM.

## 4. Zero knowledge — what leaks
Groth16 is perfectly zero-knowledge. gnark masks each in-circuit commitment
with a random value, so the lookup and range-check commitments hide the
witness too (this was not true before gnark v0.11, CVE-2024-45040; this project
uses v0.16.5). Revealed: the statement, the definitions it uses, the capacity
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
* `circuit`: honest witnesses solve; six targeted forgeries are rejected by both
  the relation and the circuit (wrong statement, cyclic self-justification,
  variable outside its context, bogus β-step, `Type : Type`, non-fresh
  congruence variable). A refinement fuzz test confirms that the circuit never
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
   (a) inductive types: recursor rows with ι-reduction in the conv table, plus
   positivity checks done publicly on declarations;
   (b) universe polymorphism: a level-expression table with `max/imax/succ`
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
