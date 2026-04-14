import KanTactics
import KanLampe.Convenience.Decide

/-!
# KanLampe.Convenience.Aesop

Native implementation of generic proof search as a bounded
disjunction over the 9 primitive `KanExtensionKind` variants.  No
call to Lean's built-in `aesop` tactic or to Mathlib's tactic
`Mathlib.Tactic.Aesop`.

## Categorical story

General-purpose proof search is a saturation procedure in the
proof category.  Given a goal `g`, the search explores the comma
category `(K | g)` where `K` is the inclusion of "structurally
reachable" proof states, looking for a factorization through a
cocone whose components are direct proofs.

Aesop structures this search as a best-first traversal with safe
rules (always applied) and unsafe rules (applied with a success
score), but the underlying proof terms it emits are built from
the same 9 primitives as every other Lean tactic.

## Reduction to the spanning set

Aesop's rule categories map to the 9 primitives as follows:

- `exact`/`assumption` rules → **Identity** (`kan_exact`).
- `apply` rules → **Precomposition** (`kan_apply`).
- `intro`/`intros` rules → **Adjunction unit** (`kan_intros`).
- `cases`/`rcases` rules → **Decomposition** (`kan_cases`).
- `constructor`/`refine ⟨_, _⟩` rules → **Precomposition** (`kan_refine`)
  or **Colimit injection** (`kan_constructor`).
- `simp`/`simp_all` rules → **Normalize** (`kan_simp`).
- `induction` rules → **Initial algebra** (`kan_induction`).

No new `KanExtensionKind` is introduced.  Aesop is a search
strategy over the 9 primitives, not an extension of them.

## Implementation: bounded saturation

The first-pass implementation is a finite disjunction covering the
most common structural shapes encountered in the lampe port:

1. **Trivial closure**: `kan_rfl`, `kan_decide`, and the assumption
   check via `kan_assumption` (see below).
2. **Implication introduction**: `kan_intros` to move hypotheses
   into context, then retry the closure checks.
3. **Constructor application**: for goals whose head is an inductive
   type, invoke `kan_constructor` and retry on each subgoal.
4. **Normalization**: `kan_simp` as a final simplification pass.

The primary path here is intentionally conservative.  It handles the
structural reasoning used in lampe for lifting Hoare triples,
decomposing separation-logic assertions, and discharging existential
witnesses.  More sophisticated goal-directed heuristics (best-first
scoring, rule priorities, red-herring detection) live in a future
`KanLampe.Aesop.Saturate` module.

## The `kan_assumption` helper

`kan_assumption` iterates the local context and invokes `kan_exact h`
(the Identity primitive) for each free variable `h`, returning the
first success.  This is automation *over* the Identity family, not
a new extension kind.

The invariant preserved is: every proof term emitted by `kan_aesop`
and `kan_assumption` is built from the 9 primitive `KanExtensionKind`
variants.
-/

open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Native assumption check via iterated `kan_exact`.

    Iterates the local context and invokes the Identity Kan extension
    primitive (`kan_exact`) on each free variable, returning the
    first success.  Each attempted step is a call to `kanExtend
    (.identityExact ·)`, which is the Identity primitive's entry
    point.  This is automation over the Identity family, not a
    direct kernel assignment bypassing the 9-primitive layer. -/
elab "kan_assumption" : tactic => do
  let mvarId <- getMainGoal
  mvarId.withContext do
    let ctx <- getLCtx
    let target <- instantiateMVars (<- mvarId.getType)
    let mut closed := false
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      if closed then
        break
      let hypType <- instantiateMVars localDecl.type
      if (<- withNewMCtxDepth (isDefEq hypType target)) then
        let savedState <- saveState
        try
          let hypIdent := mkIdent localDecl.userName
          evalTactic (<- `(tactic| kan_exact $hypIdent))
          closed := true
        catch _ =>
          restoreState savedState
    if !closed then
      failure

/-- Try a tactic, restoring state on failure. -/
private def tryKan (t : TacticM Unit) : TacticM Bool := do
  let savedState <- saveState
  try
    t
    return true
  catch _ =>
    restoreState savedState
    return false

/-- Safe reflexivity check: only invoke `kan_rfl` when the goal is
    an `Eq` application or definitionally `True`.  This avoids the
    upstream issue in `identityExact` where `elabTerm` assigns `rfl`
    with unresolved metavariables to non-equality goals. -/
elab "kan_rfl_safe" : tactic => do
  let mvarId <- getMainGoal
  let target <- instantiateMVars (<- mvarId.getType)
  if target.isAppOf ``Eq then
    evalTactic (<- `(tactic| kan_rfl))
  else if target.isAppOf ``True then
    evalTactic (<- `(tactic| kan_exact True.intro))
  else if (<- isDefEq target (mkConst ``True)) then
    evalTactic (<- `(tactic| kan_exact True.intro))
  else
    failure

/-- Native `aesop` via the spanning set (bounded saturation).

    Each branch is tried with explicit state save/restore to avoid
    MetaM state leakage across branches.  See the module docstring
    for the categorical justification and the list of rule shapes. -/
elab "kan_aesop" : tactic => do
  if (<- tryKan (evalTactic (<- `(tactic| kan_assumption)))) then return
  if (<- tryKan (evalTactic (<- `(tactic| kan_rfl_safe)))) then return
  if (<- tryKan (evalTactic (<- `(tactic| (kan_constructor; all_goals (first | kan_assumption | kan_rfl_safe)))))) then return
  if (<- tryKan (evalTactic (<- `(tactic| (kan_intros; first | kan_assumption | kan_rfl_safe))))) then return
  if (<- tryKan (evalTactic (<- `(tactic| kan_simp)))) then return
  failure
