import KanTactics

/-!
# KanLampe.Convenience.SimpByName

A variant of `kan_simp_only` that resolves lemma names directly
via the environment lookup, bypassing `elabTerm`.  This avoids
stuck typeclass resolution on polymorphic lemmas like `add_comm`,
`mul_comm`, etc., where the type argument is not yet determined.

Additionally, this module uses `simpTarget` rather than calling
`Simp.main` directly.  The upstream `normalizeSimpOnly` in
kan-tactics passes empty `Methods {}` to `Simp.main`, which
causes the simp engine to skip all rewriting in Lean 4.30.0-rc1
(the default `post` method returns expressions unchanged).
`simpTarget` internally calls `simpCore` which sets up the
correct `mkDefaultMethodsCore` methods.

## Categorical story

Same as `kan_simp_only` (Normalize family): transport in the
sub-groupoid restricted to a specified lemma set.  The only
difference is how the lemma set is constructed: by environment
lookup rather than term elaboration.

No new `KanExtensionKind` is introduced.
-/

open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Simp-only with lemma names resolved via environment lookup,
    bypassing term elaboration.  Uses `simpTarget` to ensure the
    simp rewriting engine is active.

    Categorically: Normalize restricted to the given lemma set
    (same as `normalizeSimpOnly`). -/
elab "kan_simp_names " "[" lemmas:ident,* "]" : tactic => do
  let mvarId <- getMainGoal
  mvarId.withContext do
    let env <- getEnv
    let simpTheorems <- lemmas.getElems.foldlM (fun acc stx => do
      let n := stx.getId.eraseMacroScopes
      if env.contains n then
        acc.addConst n
      else
        failure
      ) ({} : SimpTheorems)
    let congrTheorems <- getSimpCongrTheorems
    let ctx <- Simp.mkContext
      (simpTheorems := #[simpTheorems])
      (congrTheorems := congrTheorems)
    let ctx := ctx.setFailIfUnchanged false
    let (result, _) <- simpTarget mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])

/-- Full simp with the default lemma set, using `simpTarget`.
    Workaround for upstream kan-tactics `kan_simp` which passes
    empty Methods to Simp.main in Lean 4.30.0-rc1. -/
elab "kan_simp_fixed" : tactic => do
  let mvarId <- getMainGoal
  mvarId.withContext do
    let simpTheorems <- getSimpTheorems
    let congrTheorems <- getSimpCongrTheorems
    let ctx <- Simp.mkContext
      (simpTheorems := #[simpTheorems])
      (congrTheorems := congrTheorems)
    let (result, _) <- simpTarget mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])

