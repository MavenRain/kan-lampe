import KanTactics

/-!
# KanLampe.Convenience.Decide

Native implementation of `decide` as a sequence of kan-tactics
primitives.  No call to Lean's built-in `decide` tactic.

## Categorical story

The `Decidable` typeclass witnesses that membership in a proposition
is a computable function `p → Bool`.  Decidable propositions form
a sub-subcategory `Decidable ↪ Prop`.  The `decide` tactic is the
left Kan extension along this inclusion:

    (Lan_{Decidable ↪ Prop} F)(p) = F(p) when `p` is decidable

where F maps a decidable `p` with instance `Decidable.isTrue h` to
the witness `h : p`.

## Reduction to the spanning set

1. **Precomposition** (`kan_apply`) along `of_decide_eq_true`.
2. **Identity** (`kan_rfl`) closing by kernel reduction.

## Upstream workaround

kan-tactics' `identityExact` uses `elabTerm` with the target as a
hint, then assigns without verifying that all metavariables in the
elaborated term are resolved.  On goals where `rfl` leaves pending
metavariables (e.g., `decide p = true` when `decide p` is stuck),
the assignment "succeeds" but the kernel later rejects it.

`kan_decide` works around this by checking the assigned proof for
unresolved metavariables after the combined apply+rfl sequence.  If
any remain, it rolls back and fails.
-/

open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Native `decide` via the spanning set.

    Runs `kan_apply of_decide_eq_true` followed by `kan_rfl`,
    then validates the proof has no unresolved metavariables.
    Atomic: restores state on failure. -/
elab "kan_decide" : tactic => do
  let savedState <- saveState
  let originalGoal <- match (<- getGoals) with
    | g :: _ => pure g
    | [] => failure
  let succeeded <- tryCatch
    (do
      evalTactic (<- `(tactic| kan_apply of_decide_eq_true))
      evalTactic (<- `(tactic| kan_rfl))
      let proof <- instantiateMVars (mkMVar originalGoal)
      pure (!proof.hasExprMVar))
    (fun _ => pure false)
  if succeeded then
    pure ()
  else
    restoreState savedState
    failure
