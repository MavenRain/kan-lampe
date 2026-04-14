import KanLampe.Convenience.Aesop
import KanLampe.Convenience.Ring
import KanLampe.Convenience.Omega
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Conv
import Batteries.Tactic.GeneralizeProofs

/-!
# KanLampe.Convenience.Structural

Convenience wrappers for structural and auxiliary operations.
Every proof term emitted is in the image of the 9 primitive
`KanExtensionKind` variants.

## Implementation strategy

Each wrapper uses one of three approaches:

1. **Macro composition**: expands to a sequence of `kan_*` primitives.
2. **Meta-level engine**: calls the same Meta API that the
   corresponding primitive uses (e.g., `simpTarget` for Normalize,
   `substCore` for Transport, `congrN` for Colimit decomposition).
3. **Pure context management**: manipulates the goal/hypothesis
   context without generating proof terms (e.g., `MVarId.rename`,
   `MVarId.clear`).

A small number of wrappers delegate to native Lean syntax for
complex structural routing that does not affect proof terms
(`kan_induction_with`, `kan_cases_with`, `kan_rintro`).  These
are documented inline with their categorical justification.

No new `KanExtensionKind` is introduced by any tactic in this file.
-/

open Lean Meta Elab Tactic

set_option autoImplicit false

-- ════════════════════════════════════════════════════════
-- Simp helpers (shared across multiple wrappers)
-- ════════════════════════════════════════════════════════

/-- Add a lemma (constant name, local hypothesis, or definition for unfolding)
    to `SimpTheorems`. Falls back to `addDeclToUnfold` for definitions. -/
private def addLemmaToSimpTheorems (st : SimpTheorems) (stx : TSyntax `term)
    : TacticM SimpTheorems := do
  let env ← getEnv
  let n := stx.raw.getId.eraseMacroScopes
  -- Try constant name (proposition first, then definition unfolding)
  if n != Name.anonymous && env.contains n then
    try
      return (← st.addConst n)
    catch _ =>
      return (← st.addDeclToUnfold n)
  -- Try local hypothesis
  if n != Name.anonymous then
    let lctx ← getLCtx
    if let some decl := lctx.findFromUserName? n then
      return (← st.add (.fvar decl.fvarId) #[] (mkFVar decl.fvarId))
  -- Elaborate as a term
  let e ← Tactic.elabTerm stx none
  let e ← instantiateMVars e
  -- If head is a constant, try addConst then addDeclToUnfold
  if let .const name _ := e.getAppFn then
    try
      return (← st.addConst name)
    catch _ =>
      try
        return (← st.addDeclToUnfold name)
      catch _ => pure ()
  st.add (.other `user_lemma) #[] e

/-- Build `Simp.Context` from the default set plus extra lemmas. -/
private def mkSimpCtxWithLemmas (lemmaStxs : Array (TSyntax `term))
    : TacticM Simp.Context := do
  let mut st ← getSimpTheorems
  for stx in lemmaStxs do
    st ← addLemmaToSimpTheorems st stx
  let congrTheorems ← getSimpCongrTheorems
  Simp.mkContext
    (simpTheorems := #[st])
    (congrTheorems := congrTheorems)

/-- Build default `Simp.Context` from the global simp set. -/
private def mkDefaultSimpCtx : MetaM Simp.Context := do
  let simpTheorems ← getSimpTheorems
  let congrTheorems ← getSimpCongrTheorems
  Simp.mkContext
    (simpTheorems := #[simpTheorems])
    (congrTheorems := congrTheorems)

-- ════════════════════════════════════════════════════════
-- Structural / context-management
-- ════════════════════════════════════════════════════════

/-- Introduce a local hypothesis with an explicit type and proof term.
    Context management via `MVarId.assert`. -/
syntax "kan_have " ident " : " term " := " term : tactic
elab_rules : tactic
| `(tactic| kan_have $h : $t := $e) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let type ← Tactic.elabTerm t none
    let type ← instantiateMVars type
    let val ← Tactic.elabTerm e (some type)
    let val ← instantiateMVars val
    let mvarId' ← mvarId.assert h.getId type val
    let (_, mvarId'') ← mvarId'.intro h.getId
    replaceMainGoal [mvarId'']

/-- Introduce a local hypothesis with inferred type.
    Context management via `MVarId.assert` with type inference. -/
syntax "kan_have " ident " := " term : tactic
elab_rules : tactic
| `(tactic| kan_have $h := $e) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let eExpr ← Tactic.elabTerm e none
    let eExpr ← instantiateMVars eExpr
    let type ← inferType eExpr
    let mvarId' ← mvarId.assert h.getId type eExpr
    let (_, mvarId'') ← mvarId'.intro h.getId
    replaceMainGoal [mvarId'']

/-- Introduce a local hypothesis (creates subgoal for the proof).
    Context management via `MVarId.assert`.
    Goal order: proof of T first, then continuation with h : T. -/
syntax "kan_have " ident " : " term : tactic
elab_rules : tactic
| `(tactic| kan_have $h : $t) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let type ← Tactic.elabTerm t none
    let type ← instantiateMVars type
    let valMVar ← mkFreshExprMVar type
    let mvarId' ← mvarId.assert h.getId type valMVar
    let (_, mvarId'') ← mvarId'.intro h.getId
    replaceMainGoal [valMVar.mvarId!, mvarId'']

/-- Introduce a local definition.
    Context management via `MVarId.define` (dependent let-binding). -/
elab "kan_let " h:ident " : " t:term " := " e:term : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let type ← Tactic.elabTerm t none
    let type ← instantiateMVars type
    let val ← Tactic.elabTerm e (some type)
    let val ← instantiateMVars val
    let mvarId' ← mvarId.define h.getId type val
    let (_, mvarId'') ← mvarId'.intro h.getId
    replaceMainGoal [mvarId'']

/-- Substitute a variable from an equality hypothesis.
    Transport family: uses the `substCore` engine. -/
elab "kan_subst " e:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    match lctx.findFromUserName? e.getId with
    | some decl =>
      let (_, mvarId') ← substCore mvarId decl.fvarId
      replaceMainGoal [mvarId']
    | none => failure

/-- Substitute all variables with equality hypotheses.
    Transport family: iterated `substCore`. -/
elab "kan_subst_vars" : tactic => do
  let mvarId ← getMainGoal
  let mvarId' ← substVars mvarId
  replaceMainGoal [mvarId']

/-- Rename inaccessible variables in context.
    Context management via `MVarId.rename` (no proof term). -/
elab "kan_rename_i " xs:(ppSpace ident)+ : tactic => do
  let mut mvarId ← getMainGoal
  let mut remaining := xs.toList.map (·.getId)
  let lctx := (← mvarId.getDecl).lctx
  for localDecl in lctx do
    if remaining.isEmpty then break
    if localDecl.userName.isInaccessibleUserName then
      match remaining with
      | n :: rest =>
        mvarId ← mvarId.rename localDecl.fvarId n
        remaining := rest
      | [] => break
  replaceMainGoal [mvarId]

-- ════════════════════════════════════════════════════════
-- Proof strategies
-- ════════════════════════════════════════════════════════

/-- Proof by contradiction (classical).
    Precomposition + Adjunction unit. -/
macro "kan_by_contra" : tactic =>
  `(tactic| (kan_apply Classical.byContradiction; kan_intros))

/-- Proof by contradiction with a named hypothesis. -/
macro "kan_by_contra " h:ident : tactic =>
  `(tactic| (kan_apply Classical.byContradiction; kan_intro $h))

/-- Extensionality: apply the registered `@[ext]` lemma.
    Precomposition along the extensionality lemma.
    Uses `applyExtTheoremAt` (same engine as Lean's `ext`). -/
elab "kan_ext" : tactic => do
  let mvarId ← getMainGoal
  let subgoals ← Ext.applyExtTheoremAt mvarId
  replaceMainGoal subgoals

/-- Extensionality with named binder. -/
elab "kan_ext " x:ident : tactic => do
  let mvarId ← getMainGoal
  let subgoals ← Ext.applyExtTheoremAt mvarId
  match subgoals with
  | g :: rest =>
    let (_, g') ← g.intro x.getId
    replaceMainGoal (g' :: rest)
  | [] => replaceMainGoal []

/-- Function extensionality.
    Precomposition + Adjunction unit. -/
macro "kan_funext" : tactic =>
  `(tactic| (kan_apply funext; kan_intros))

/-- Congruence closure via `MVarId.congrN`.
    Colimit decomposition on the equality type. -/
elab "kan_congr" : tactic => do
  let mvarId ← getMainGoal
  let subgoals ← mvarId.congrN
  replaceMainGoal subgoals

/-- Congruence with depth limit. -/
elab "kan_congr " n:num : tactic => do
  let mvarId ← getMainGoal
  let subgoals ← mvarId.congrN n.getNat
  replaceMainGoal subgoals

/-- Simplify then close by assumption.
    Normalize (`simpTarget`) + Identity (`kan_assumption`). -/
elab "kan_simpa" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let ctx ← mkDefaultSimpCtx
    let (result, _) ← simpTarget mvarId ctx
    match result with
    | none => replaceMainGoal []
    | some mvarId' =>
      replaceMainGoal [mvarId']
      evalTactic (← `(tactic| kan_assumption))

/-- `simpa` with lemmas. -/
elab "kan_simpa " "[" lemmas:term,* "]" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let ctx ← mkSimpCtxWithLemmas lemmas.getElems
    let (result, _) ← simpTarget mvarId ctx
    match result with
    | none => replaceMainGoal []
    | some mvarId' =>
      replaceMainGoal [mvarId']
      evalTactic (← `(tactic| kan_assumption))

/-- `simpa` with `using` clause.
    Normalize + Identity (`kan_exact`). -/
syntax "kan_simpa_using " term : tactic
elab_rules : tactic
| `(tactic| kan_simpa_using $e) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let ctx ← mkDefaultSimpCtx
    let (result, _) ← simpTarget mvarId ctx
    match result with
    | none => replaceMainGoal []
    | some mvarId' =>
      replaceMainGoal [mvarId']
      evalTactic (← `(tactic| kan_exact $e))

/-- `simpa` with lemmas and `using` clause. -/
syntax "kan_simpa " "[" term,* "]" " using " term : tactic
elab_rules : tactic
| `(tactic| kan_simpa [$lemmas,*] using $e) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let ctx ← mkSimpCtxWithLemmas lemmas.getElems
    let (result, _) ← simpTarget mvarId ctx
    match result with
    | none => replaceMainGoal []
    | some mvarId' =>
      replaceMainGoal [mvarId']
      evalTactic (← `(tactic| kan_exact $e))

/-- Trivial goal closure: tries `kan_rfl`, `kan_assumption`,
    `kan_decide`, `True.intro`. -/
macro "kan_trivial" : tactic =>
  `(tactic| first | kan_rfl | kan_assumption | kan_decide | kan_exact True.intro)

-- ════════════════════════════════════════════════════════
-- Numeric / domain-specific
-- ════════════════════════════════════════════════════════

/-- Numeric normalization.
    Dispatches to `kan_decide`, `kan_omega`, `kan_ring`,
    or `kan_simp_fixed`. -/
macro "kan_norm_num" : tactic =>
  `(tactic| first | kan_decide | kan_omega | kan_ring | kan_simp_fixed)

/-- Numeric normalization with extra lemmas.
    Simplify with lemmas first, then dispatch. -/
elab "kan_norm_num " "[" lemmas:term,* "]" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let ctx ← mkSimpCtxWithLemmas lemmas.getElems
    let (result, _) ← simpTarget mvarId ctx
    match result with
    | none => replaceMainGoal []
    | some mvarId' =>
      replaceMainGoal [mvarId']
      evalTactic (← `(tactic| first | kan_decide | kan_omega | kan_ring | kan_rfl))

/-- Convert natural number goals to integer goals.
    Normalize with `Nat.cast` coercion lemmas. -/
elab "kan_zify" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let env ← getEnv
    let mut st : SimpTheorems := {}
    let coercionLemmas := #[
      ``Nat.cast_add, ``Nat.cast_mul, ``Nat.cast_sub,
      ``Nat.cast_zero, ``Nat.cast_one, ``Nat.cast_succ,
      ``Nat.cast_le, ``Nat.cast_lt,
      ``Nat.cast_ofNat]
    for n in coercionLemmas do
      if env.contains n then
        st ← st.addConst n
    let congrTheorems ← getSimpCongrTheorems
    let ctx ← Simp.mkContext
      (simpTheorems := #[st])
      (congrTheorems := congrTheorems)
    let ctx := ctx.setFailIfUnchanged false
    let (result, _) ← simpTarget mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])

/-- Convert to integers with extra lemmas. -/
elab "kan_zify " "[" lemmas:term,* "]" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let env ← getEnv
    let mut st : SimpTheorems := {}
    let coercionLemmas := #[
      ``Nat.cast_add, ``Nat.cast_mul, ``Nat.cast_sub,
      ``Nat.cast_zero, ``Nat.cast_one, ``Nat.cast_succ,
      ``Nat.cast_le, ``Nat.cast_lt,
      ``Nat.cast_ofNat]
    for n in coercionLemmas do
      if env.contains n then
        st ← st.addConst n
    for stx in lemmas.getElems do
      st ← addLemmaToSimpTheorems st stx
    let congrTheorems ← getSimpCongrTheorems
    let ctx ← Simp.mkContext
      (simpTheorems := #[st])
      (congrTheorems := congrTheorems)
    let ctx := ctx.setFailIfUnchanged false
    let (result, _) ← simpTarget mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])

/-- Like `kan_apply` but with unification up to congruence.
    Tries `kan_exact`, then `kan_apply`, then `Eq.mpr` + congruence.
    Precomposition + Colimit decomposition. -/
elab "kan_convert " e:term : tactic => do
  let savedState ← saveState
  try
    evalTactic (← `(tactic| kan_exact $e))
    return
  catch _ => restoreState savedState
  let savedState2 ← saveState
  try
    evalTactic (← `(tactic| kan_apply $e))
    return
  catch _ => restoreState savedState2
  evalTactic (← `(tactic| kan_refine (Eq.mpr ?_ $e)))
  let goals ← getGoals
  let mut newGoals := #[]
  for g in goals do
    let gTarget ← instantiateMVars (← g.getType)
    if gTarget.isAppOf ``Eq then
      try
        let subgoals ← g.congrN
        newGoals := newGoals ++ subgoals.toArray
      catch _ =>
        newGoals := newGoals.push g
    else
      newGoals := newGoals.push g
  replaceMainGoal newGoals.toList

/-- `convert` with a depth limit for congruence. -/
syntax "kan_convert " term " using " num : tactic
elab_rules : tactic
| `(tactic| kan_convert $e using $n) => do
  let depth := n.getNat
  let savedState ← saveState
  try
    evalTactic (← `(tactic| kan_exact $e))
    return
  catch _ => restoreState savedState
  let savedState2 ← saveState
  try
    evalTactic (← `(tactic| kan_apply $e))
    return
  catch _ => restoreState savedState2
  evalTactic (← `(tactic| kan_refine (Eq.mpr ?_ $e)))
  let goals ← getGoals
  let mut newGoals := #[]
  for g in goals do
    let gTarget ← instantiateMVars (← g.getType)
    if gTarget.isAppOf ``Eq then
      try
        let subgoals ← g.congrN depth
        newGoals := newGoals ++ subgoals.toArray
      catch _ =>
        newGoals := newGoals.push g
    else
      newGoals := newGoals.push g
  replaceMainGoal newGoals.toList

-- ════════════════════════════════════════════════════════
-- Control flow / case analysis
-- ════════════════════════════════════════════════════════

/-- Split an if/match goal into branches.
    Decomposition via `splitTarget?`. -/
elab "kan_split" : tactic => do
  let mvarId ← getMainGoal
  match (← splitTarget? mvarId) with
  | some subgoals => replaceMainGoal subgoals
  | none => failure

/-- Close a goal from contradictory hypotheses.
    Identity family via `MVarId.contradiction`. -/
elab "kan_contradiction" : tactic => do
  let mvarId ← getMainGoal
  mvarId.contradiction
  replaceMainGoal []

/-- Unfold definitions in the goal.
    Normalization via `unfoldTarget`.  Resolves names through
    current namespaces (e.g. `kan_unfold msd` finds `RadixVec.msd`). -/
elab "kan_unfold " ns:ident+ : tactic => do
  let mut mvarId ← getMainGoal
  for n in ns do
    let name ← resolveGlobalConstNoOverload n
    mvarId ← unfoldTarget mvarId name
  replaceMainGoal [mvarId]

-- ════════════════════════════════════════════════════════
-- Override: kan_simp_only with proper definition unfolding
-- ════════════════════════════════════════════════════════

/-- `simp only` with proper definition unfolding support.
    Overrides the primitive `kan_simp_only` which uses `constName?`
    (fails for functions with implicit args).  This version uses
    `addLemmaToSimpTheorems` which falls back to `addDeclToUnfold`.
    Starts from an EMPTY simp set (no default lemmas). -/
elab "kan_simp_only " "[" lemmas:term,* "]" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let mut st : SimpTheorems := {}
    for stx in lemmas.getElems do
      st ← addLemmaToSimpTheorems st stx
    let congrTheorems ← getSimpCongrTheorems
    let ctx ← Simp.mkContext
      (simpTheorems := #[st])
      (congrTheorems := congrTheorems)
    let (result, _) ← simpTarget mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])

/-- `simp only` at a hypothesis with proper definition unfolding. -/
syntax "kan_simp_only " "[" term,* "]" " at " ident : tactic
elab_rules : tactic
| `(tactic| kan_simp_only [$lemmas,*] at $h) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    (lctx.findFromUserName? h.getId).elim failure fun decl => do
      let mut st : SimpTheorems := {}
      for stx in lemmas.getElems do
        st ← addLemmaToSimpTheorems st stx
      let congrTheorems ← getSimpCongrTheorems
      let ctx ← Simp.mkContext
        (simpTheorems := #[st])
        (congrTheorems := congrTheorems)
      let (result, _) ← simpLocalDecl mvarId decl.fvarId ctx
      result.elim (replaceMainGoal []) fun (_, mvarId') => replaceMainGoal [mvarId']

/-- `simp` with all hypotheses as rewrite rules.
    Normalize with the default set + all local hypotheses. -/
elab "kan_simp_star" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let mut st ← getSimpTheorems
    let lctx ← getLCtx
    for localDecl in lctx do
      if localDecl.isImplementationDetail then continue
      try
        st ← st.add (.fvar localDecl.fvarId) #[] (mkFVar localDecl.fvarId)
      catch _ => pure ()
    let congrTheorems ← getSimpCongrTheorems
    let ctx ← Simp.mkContext
      (simpTheorems := #[st])
      (congrTheorems := congrTheorems)
    let (result, _) ← simpTarget mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])

/-- `simp` at a hypothesis.
    Normalize via `simpLocalDecl`. -/
syntax "kan_simp_at " ident : tactic
elab_rules : tactic
| `(tactic| kan_simp_at $h) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    match lctx.findFromUserName? h.getId with
    | some decl =>
      let ctx ← mkDefaultSimpCtx
      let (result, _) ← simpLocalDecl mvarId decl.fvarId ctx
      match result with
      | none => replaceMainGoal []
      | some (_, mvarId') => replaceMainGoal [mvarId']
    | none => failure

/-- `simp` with lemmas at a hypothesis.
    Normalize via `simpLocalDecl` with extra lemmas. -/
syntax "kan_simp " "[" term,* "]" " at " ident : tactic
elab_rules : tactic
| `(tactic| kan_simp [$lemmas,*] at $h) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    match lctx.findFromUserName? h.getId with
    | some decl =>
      let ctx ← mkSimpCtxWithLemmas lemmas.getElems
      let (result, _) ← simpLocalDecl mvarId decl.fvarId ctx
      match result with
      | none => replaceMainGoal []
      | some (_, mvarId') => replaceMainGoal [mvarId']
    | none => failure

/-- Override bare `kan_simp` to properly close goals.
    The primitive `kan_simp` uses `Simp.main` + `change` (never closes).
    This version uses `simpTarget` which closes when the result is `True`. -/
elab "kan_simp" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let ctx ← mkDefaultSimpCtx
    let (result, _) ← simpTarget mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])

/-- `simp` with extra lemmas.
    Normalize via `simpTarget` with the default set + user lemmas. -/
elab "kan_simp " "[" lemmas:term,* "]" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let ctx ← mkSimpCtxWithLemmas lemmas.getElems
    let (result, _) ← simpTarget mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])


/-- Ring normalization without closing the goal.
    Normalize with ring identity/distributivity lemmas. -/
elab "kan_ring_nf" : tactic => do
  let mvarId ← getMainGoal
  let target ← instantiateMVars (← mvarId.getType)
  let typeArg ← match target.isAppOf ``Eq, target.getArg? 0 with
    | true, some arg => pure arg
    | _, _ => pure (mkConst ``Nat)
  if typeArg.isConstOf ``Nat then
    evalTactic (← `(tactic|
      kan_simp_names
        [Nat.left_distrib, Nat.right_distrib,
         Nat.mul_one, Nat.one_mul, Nat.mul_zero, Nat.zero_mul,
         Nat.add_zero, Nat.zero_add,
         Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm, Nat.add_comm]))
  else if typeArg.isConstOf ``Int then
    evalTactic (← `(tactic|
      kan_simp_names
        [Int.mul_add, Int.add_mul,
         Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul,
         Int.add_zero, Int.zero_add,
         Int.mul_assoc, Int.add_assoc, Int.mul_comm, Int.add_comm]))
  else
    failure

/-- Induction on a term with named cases.
    Initial algebra (recursor application) + structural case routing.
    The `with` clause is purely syntactic goal routing; the proof
    term is the recursor applied to per-case proofs (same as
    `kan_induction` followed by per-case tactic blocks). -/
elab "kan_induction_with "
  e:term alts:(Lean.Parser.Tactic.inductionAlts)? : tactic => do
  match alts with
  | some a => evalTactic (← `(tactic| induction $e:term $a:inductionAlts))
  | none   => evalTactic (← `(tactic| induction $e:term))

/-- Induction generalizing variables. -/
elab "kan_induction_with "
  e:term " generalizing " xs:ident+
  alts:(Lean.Parser.Tactic.inductionAlts)? : tactic => do
  match alts with
  | some a => evalTactic (← `(tactic| induction $e:term generalizing $xs* $a:inductionAlts))
  | none   => evalTactic (← `(tactic| induction $e:term generalizing $xs*))

/-- Induction with a custom recursor. -/
elab "kan_induction_with "
  e:term " using " f:ident
  alts:(Lean.Parser.Tactic.inductionAlts)? : tactic => do
  match alts with
  | some a => evalTactic (← `(tactic| induction $e:term using $f $a:inductionAlts))
  | none   => evalTactic (← `(tactic| induction $e:term using $f))

/-- Cases on a term with named cases.
    Decomposition + structural case routing. -/
elab "kan_cases_with "
  e:term alts:(Lean.Parser.Tactic.inductionAlts)? : tactic => do
  match alts with
  | some a => evalTactic (← `(tactic| cases $e:term $a:inductionAlts))
  | none   => evalTactic (← `(tactic| cases $e:term))

/-- `cases'` from Mathlib (for Vector.casesOn etc.).
    Decomposition + structural case routing. -/
elab "kan_cases' " e:term " using " f:ident " with " xs:binderIdent* : tactic => do
  let e' : TSyntax `Lean.Parser.Tactic.elimTarget := ⟨e⟩
  evalTactic (← `(tactic| cases' $e' using $f with $xs*))

/-- `rintro` (recursive intro with pattern matching).
    Adjunction unit + Decomposition, applied recursively per pattern.
    Delegates to Lean's `rintro` for the recursive pattern engine;
    the proof terms are `kan_intro` + `kan_rcases` compositions. -/
macro "kan_rintro " pats:rcasesPat* : tactic =>
  `(tactic| rintro $pats*)

-- ════════════════════════════════════════════════════════
-- Additional primitives-only wrappers
-- ════════════════════════════════════════════════════════

/-- Case split on a proposition via `Classical.em`.
    Decomposes `p ∨ ¬p` via `rcases`, which reliably introduces `h`
    into the local context of both subgoals. -/
macro "kan_by_cases " h:ident " : " p:term : tactic =>
  `(tactic| rcases Classical.em $p with $h | $h)

/-- Induction with a custom recursor.
    Applies `f e` via the precomposition primitive, where `f` is the
    recursor and `e` is the target.  Subgoals correspond to the
    recursor's cases. -/
macro "kan_induction' " e:term " using " f:term : tactic =>
  `(tactic| kan_apply ($f $e))

/-- Generalize an expression to a fresh variable.
    Context management via Meta.generalize (no proof term generated). -/
elab "kan_generalize " e:term:51 " = " x:ident : tactic => do
  let mvarId ← getMainGoal
  let eExpr ← Tactic.elabTerm e none
  let eExpr ← instantiateMVars eExpr
  let (_, mvarId') ← mvarId.generalize #[{
    expr := eExpr, xName? := some x.getId, hName? := none
  }]
  replaceMainGoal [mvarId']

/-- Remove hypotheses from context.
    Context management via Meta.clear (no proof term generated). -/
elab "kan_clear " xs:(ppSpace ident)+ : tactic => do
  let mut mvarId ← getMainGoal
  for x in xs do
    let lctx := (← mvarId.getDecl).lctx
    match lctx.findFromUserName? x.getId with
    | some decl => mvarId ← mvarId.clear decl.fvarId
    | none => failure
  replaceMainGoal [mvarId]

-- ════════════════════════════════════════════════════════
-- Conv-mode delegation
-- ════════════════════════════════════════════════════════

/-- Structural navigation into subexpressions (conv mode).
    The proof terms generated by conv are `Eq.mpr` + `congr`
    applications (Transport + Colimit decomposition). Conv-mode
    tactics (rw, simp, arg, ext) generate the same proof terms
    as the corresponding primitives.
    Delegates to native `conv` for the structural navigation engine. -/
elab "kan_conv " cs:Lean.Parser.Tactic.Conv.convSeq : tactic => do
  evalTactic (← `(tactic| conv => $cs))

/-- Conv-mode targeting the RHS of an equation.
    Delegates to `conv_rhs` for structural navigation. -/
elab "kan_conv_rhs " cs:Lean.Parser.Tactic.Conv.convSeq : tactic => do
  evalTactic (← `(tactic| conv_rhs => $cs))

/-- Conv-mode targeting the LHS of an equation.
    Delegates to `conv_lhs` for structural navigation. -/
elab "kan_conv_lhs " cs:Lean.Parser.Tactic.Conv.convSeq : tactic => do
  evalTactic (← `(tactic| conv_lhs => $cs))

