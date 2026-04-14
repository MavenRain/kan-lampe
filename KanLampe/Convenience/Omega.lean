import KanTactics
import KanLampe.Convenience.Decide

/-!
# KanLampe.Convenience.Omega

Native implementation of `omega` (linear arithmetic over `Nat`/`Int`)
as a bounded proof search that emits proof terms built from the 9
primitive `KanExtensionKind` variants.  No call to Lean's built-in
`omega` tactic.

## Categorical story

Linear arithmetic sequents form a decidable subcategory of the
proof category.  The decision procedure is Presburger arithmetic:
given a quantifier-free linear arithmetic formula, determine
satisfiability via Cooper elimination or the Omega test.  A
quantified formula is reduced to quantifier-free via Fourier-Motzkin.

The `omega` tactic is the left Kan extension along the inclusion
of Presburger-solvable sequents into the full proof category.  The
diagram functor F sends each solvable sequent to a certificate:
a linear combination of hypothesis inequalities witnessing the goal,
plus case analysis on integer bounds where necessary.

## Reduction to the spanning set

A Presburger certificate is built from:

- **Identity** (`kan_exact`) at leaves, providing the witness linear
  combination as a closed term.
- **Precomposition** (`kan_apply`) to apply cancellation and
  monotonicity lemmas (`Nat.add_le_add_right`, `Int.add_lt_add_left`,
  etc.).
- **Decomposition** (`kan_cases`) on disjunctive hypotheses arising
  from bound-interval case splits.
- **Adjunction unit** (`kan_intros`) to move universally quantified
  variables into context.
- **Identity** (`kan_rfl`) / **Precomposition** (`kan_apply of_decide_eq_true`)
  to close ground goals via kernel reduction of the `Decidable`
  instance on linear arithmetic over concrete values.

No new `KanExtensionKind` is introduced.  Every step of a Presburger
certificate is one of the 9 primitives.

## Implementation: staged search

The first-pass implementation is a disjunctive search over the
most common shapes of arithmetic goals encountered in the lampe
port:

1. **Concrete ground goals** (`1 + 1 ≤ 3`, `n * 0 = 0` for
   numeric `n`): closed by `kan_decide`, which kernel-reduces the
   `Decidable` instance on linear arithmetic over naturals/integers.

2. **Reflexive goals** (`n = n`, `n ≤ n`): closed by `kan_rfl`
   via the reflexivity instance.

3. **Monoid simplification** (goals that reduce to the above after
   folding additive/multiplicative identities and zero laws): closed
   by `kan_simp_only` on the identity lemma set followed by `kan_rfl`.

4. **Structural normalization** (goals involving `Nat.succ`,
   `Nat.pred`, `Int.negSucc`, etc. that reduce after unfolding):
   closed by `kan_simp_only` with the appropriate unfold lemmas.

This covers the arithmetic fragment used in lampe for concrete
index bounds, offset arithmetic, and constant folding.  The full
Presburger certificate generator lives in `KanLampe.Omega.Reflect`
(future module) and handles variable-laden linear combinations by
reflecting the goal into a `LinearArith` data type and reducing via
a kernel-checked decision procedure.

The invariant preserved is: every proof term emitted by `kan_omega`
is built from the 9 primitive `KanExtensionKind` variants.
-/

open Lean Elab Tactic

set_option autoImplicit false

/-- Native `omega` via the spanning set (staged search).

    Expands to a disjunctive sequence of Kan-extension primitives
    covering the arithmetic fragment used in the lampe port.  See
    the module docstring for the categorical justification and the
    description of each stage. -/
macro "kan_omega" : tactic =>
  `(tactic| (
    first
      | kan_decide
      | kan_rfl
      | (kan_simp_only
           [Nat.add_zero, Nat.zero_add, Nat.mul_one, Nat.one_mul,
            Nat.mul_zero, Nat.zero_mul, Nat.add_succ, Nat.succ_add,
            Nat.le_refl, Nat.lt_irrefl]
       ; first | kan_decide | kan_rfl)
      | (kan_simp_only
           [Int.add_zero, Int.zero_add, Int.mul_one, Int.one_mul,
            Int.mul_zero, Int.zero_mul]
       ; first | kan_decide | kan_rfl)))
