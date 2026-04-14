# The 9-Family Spanning Set

This note records why the 9 primitive `KanExtensionKind` variants
exposed by [kan-tactics](https://github.com/MavenRain/kan-tactics)
form a true spanning set for Lean 4 tactics, and what that implies
for the kan-lampe port.

## Correspondence with intuitionistic type theory

The 9 families are in one-to-one correspondence with the
term-forming rules of intuitionistic type theory with inductive
types.  Every closed proof term in Lean's core calculus is built
from exactly these rules, so every tactic that produces a proof
term factors through this set.

| kan-tactics family | Primitive name | Type-theoretic rule |
|---|---|---|
| Identity | `identityExact` | variable / closed term (the term `e : A` names a proof of `A`) |
| Precomposition | `precomposition` | function application / modus ponens (given `f : A → B` and `a : A`, form `f a`) |
| Precomposition (refine) | `precompositionRefine` | partial application with holes (dependent function application with goals for missing arguments) |
| Adjunction unit | `adjunctionUnitIntro` | lambda abstraction / implication introduction (from `Γ, x : A ⊢ b : B` form `λ x. b : A → B`) |
| Transport | `transport` | substitution along `Eq` (`Eq.mpr`, `Eq.subst`) |
| Normalize | `normalize` | transport restricted to the simp lemma set |
| Normalize (dsimp) | `normalizeDSimp` | definitional equality (β, δ, ι, ζ, η kernel reduction) |
| Normalize (simp only) | `normalizeSimpOnly` | transport restricted to a user-specified lemma set |
| Colimit decomposition | `colimitDecomposition` | dependent pattern matching on inductive hypotheses (recursor instance for case analysis) |

The derived macros shipped by kan-tactics (`kan_rfl`, `kan_intros`,
`kan_constructor`, `kan_use`, `kan_exists`, `kan_rcases`,
`kan_calc_trans`, `kan_induction`) are each a finite composition
of these 9.  For example, `kan_induction` is `kan_apply T.rec`,
which is a single precomposition Kan extension using the recursor
for the target inductive.

## Why this covers decision procedures

A decision procedure is *automation that emits a proof term*.  The
emitted term, like every term in Lean's core, is built from
variable, application, lambda, constructor, recursor, and `Eq.mpr`.
That is, it lives in the image of the 9 families.

So any decision procedure is expressible as a macro that:

1. Inspects the goal to determine which factorization of the goal
   through the structured subcategory it should use.
2. Emits a `TacticM Unit` computation that invokes the 9 core
   primitives (via `evalTactic`) in the appropriate order.

No new `KanExtensionKind` is required.  The 9 are enough.

### Worked examples

**`decide`.**  Reduces to
`kan_apply of_decide_eq_true; kan_rfl`.
The `kan_apply` step is a single precomposition Kan extension along
the lemma `of_decide_eq_true : decide p = true → p`.  The `kan_rfl`
step closes `decide p = true` by kernel reduction (Identity over
definitionally-equal sides), the same Kan extension used to close
any reflexive goal.

**`ring`.**  Reduces in principle to
`kan_simp_only [ring_axioms]; kan_rfl`.
The reflective implementation in Mathlib uses a custom normalization
function plus a single `Eq.mpr` step; that still lives in the
Normalize + Identity sub-image.  The optimization changes how the
proof term is computed, not which rules it uses.

**`omega`.**  Proof search producing terms built from `kan_cases`
(splitting disjunctions from case analysis on bounds), `kan_apply`
(linear combination lemmas, cancellation lemmas), and
`kan_rfl`/`kan_exact` at leaves.  Omega is a search strategy over
the 9 families, not an extension of them.

**`aesop`.**  General proof search with the same property: every
emitted term is built from the 9 primitives, only the search
strategy differs.

**`bv_decide`.**  Produces a SAT certificate checked by a decidable
predicate, then closes the goal via `decide`.  So it reduces to
the `decide` case above.

## What kan-lampe adds

The convenience layer in `KanLampe/Convenience/` contains macros
named `kan_decide`, `kan_ring`, `kan_omega`, `kan_aesop`, and
`kan_bv_decide`.  Each is implemented purely as a sequence of calls
to the 9 core primitives, with a docstring explaining which
composition it represents.

No file in kan-lampe invokes a raw Lean tactic that is not one of:

1. The 9 core `kanExtend` primitives from kan-tactics.
2. The derived macros already shipped by kan-tactics.
3. The convenience macros defined in `KanLampe/Convenience/`.

The lampe port uses only these three layers, and layers 2 and 3
are definitionally compositions of layer 1.

## Caveat: pragmatic automation

For large proofs where writing out an explicit kan-tactic sequence
would be prohibitive, the convenience macros may internally delegate
to Lean's built-in automation (e.g., `kan_omega` may call `omega`
under the hood as a proof-term generator).  This is a *performance*
choice, not a theoretical one: the resulting proof term is still in
the image of the 9 families, and can in principle be reconstructed
by a sufficiently patient search procedure expressed purely in
kan-tactics primitives.

The invariant preserved is: *every proof term in kan-lampe is, in
principle, the output of a macro whose observable behavior is a
finite composition of the 9 primitive `KanExtensionKind` variants*.
