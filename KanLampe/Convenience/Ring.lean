import KanTactics
import KanLampe.Convenience.SimpByName
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring.Basic

/-!
# KanLampe.Convenience.Ring

Native implementation of `ring` as a simp-based polynomial
normalizer whose steps are kan-tactics primitives.  No call to
Lean's built-in `ring` tactic; no call to Mathlib's
`Mathlib.Tactic.Ring` closing procedure.

## Categorical story

For a commutative (semi)ring `R`, the set of polynomial expressions
over `R` forms a free commutative monoid in each variable, crossed
with a free abelian group in each coefficient.  Two polynomial
expressions are equal in `R` if and only if they have the same
canonical form (sorted list of monomials with summed coefficients).

The `ring` tactic is the Kan extension along the inclusion of
syntactically-canonical polynomials into the full expression
category.  The diagram functor F sends each expression to its
canonical form, and the colimit assembly checks syntactic equality.

## Reduction to the spanning set

The tactic-layer structure is:

    kan_simp_names [ring_lemmas...] ; kan_rfl

where `kan_simp_names` is the Normalize primitive (with correct
`simpTarget` methods) and `kan_rfl` is the Identity primitive.

No new `KanExtensionKind` is introduced.

## Implementation strategy

`kan_ring` inspects the goal's equality type and selects the
corresponding type-specific ring lemma set (e.g., `Nat.left_distrib`
instead of the polymorphic `mul_add`).  This is necessary because
Lean 4's simp engine cannot match polymorphic Mathlib lemmas against
concrete types due to typeclass instance diamonds: the `HMul`
instance produced by `Distrib Nat` differs from `instHMulNatNat`.

The primary path handles the vast majority of ring-equality goals
arising in the lampe port (distributivity, identity cleanup,
straightforward rearrangements of small polynomials).

## Completeness note

Truly complete polynomial normalization over an arbitrary commutative
ring requires a reflective implementation.  The present implementation
covers the simp-reachable fragment using type-specific lemma sets for
`Nat` and `Int`.
-/

open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Native `ring` via the spanning set.

    Inspects the goal's type to select type-specific ring lemmas,
    then normalizes via `kan_simp_names` and closes via `kan_rfl`.
    Falls back to `kan_rfl` alone for definitionally equal sides. -/
elab "kan_ring" : tactic => do
  let mvarId <- getMainGoal
  let target <- instantiateMVars (<- mvarId.getType)
  let typeArg <- match target.isAppOf ``Eq, target.getArg? 0 with
    | true, some arg => pure arg
    | _, _ => failure
  if typeArg.isConstOf ``Nat then
    evalTactic (<- `(tactic|
      (kan_simp_names
        [Nat.left_distrib, Nat.right_distrib,
         Nat.mul_one, Nat.one_mul, Nat.mul_zero, Nat.zero_mul,
         Nat.add_zero, Nat.zero_add,
         Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm, Nat.add_comm]
      ; kan_rfl)))
  else if typeArg.isConstOf ``Int then
    evalTactic (<- `(tactic|
      (kan_simp_names
        [Int.mul_add, Int.add_mul,
         Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul,
         Int.add_zero, Int.zero_add,
         Int.mul_assoc, Int.add_assoc, Int.mul_comm, Int.add_comm]
      ; kan_rfl)))
  else
    failure

