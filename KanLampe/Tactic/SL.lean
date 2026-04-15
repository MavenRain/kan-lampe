import KanLampe.SeparationLogic.State
import KanLampe.SeparationLogic.SLP
import KanLampe.Tactic.SL.Term
import KanLampe.Tactic.SL.Init

import Lean.Meta.Tactic.Simp.Main

/-!
# KanLampe.Tactic.SL

Port of `Lampe.Tactic.SL`.  Contains the `Internal` bookkeeping
lemmas used to drive the `sl` tactic, together with the
metaprogramming pipeline (`solveEntailment'`, `solveEntailment`,
`solveSingletonStarMV`, ...) and the `sl` tactic elaborator.

Internal bookkeeping lemma proofs are left as `sorry`; the
metaprogramming pipeline is a verbatim port with namespaces renamed
to `KanLampe` and `Lean.exceptEmoji` replaced by `Except.emoji`.
-/

open KanLampe

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq

namespace KanLampe.SL

namespace Internal

theorem shift_exists_to_mvar {α β : Type _} [LawfulHeap β]
    {P R : α → SLP β} {Q : SLP β}
  : (∀ x, (P x ⊢ Q ⋆ R x)) → ((∃∃ x, P x) ⊢ Q ⋆ (∃∃ x, R x)) := by
  sorry

theorem solve_unit_star_mv {p : Prime} {P : SLP (State p)} : (P ⊢ ⟦⟧ ⋆ P) := by
  sorry

theorem singleton_congr_star_mv {p : Prime} {r} {v₁ v₂ : AnyValue p} (heq : v₁ = v₂)
  : ([r ↦ v₁] ⊢ [r ↦ v₂] ⋆ ⟦⟧) := by
  sorry

theorem lmbSingleton_congr_star_mv
    {argTps : List Tp} {outTp : Tp} {p : Prime}
    {r : FuncRef argTps outTp}
    {f₁ f₂ : HList (Tp.denote p) argTps → Expr (Tp.denote p) outTp}
    (heq : f₁ = f₂)
  : ([λr ↦ f₁] ⊢ [λr ↦ f₂] ⋆ ⟦⟧) := by
  sorry

theorem entails_self_true {p : Prime} {R : SLP (State p)} : R ⊢ R ⋆ ⟦⟧ := by
  sorry

theorem singleton_congr_star {p : Prime} {r} {v₁ v₂ : AnyValue p}
    {R : SLP (State p)} (h : v₁ = v₂)
  : [r ↦ v₁] ⋆ R ⊢ [r ↦ v₂] ⋆ R := by
  sorry

theorem lmbSingleton_congr_star {p : Prime} {i : List Tp} {o : Tp}
    {r : FuncRef i o}
    {v₁ v₂ : HList (Tp.denote p) i → Expr (Tp.denote p) o}
    {R : SLP (State p)}
    (h : v₁ = v₂)
  : [λr ↦ v₁] ⋆ R ⊢ [λr ↦ v₂] ⋆ R := by
  sorry

theorem skip_impure_evidence {α : Type _} [LawfulHeap α] {R L G H : SLP α}
  : (R ⊢ G ⋆ H) → (L ⋆ R ⊢ G ⋆ L ⋆ H) := by
  sorry

theorem skip_pure_evidence {α : Type _} [LawfulHeap α] {P : Prop}
    {H Q R : SLP α}
  : (P → (H ⊢ Q ⋆ R)) → ((⟦P⟧ : SLP α) ⋆ H ⊢ Q ⋆ (⟦P⟧ : SLP α) ⋆ R) := by
  sorry

theorem skip_final_pure_evidence {α : Type _} [LawfulHeap α] {P : Prop}
    {Q R : SLP α}
  : (P → (⟦⟧ ⊢ Q ⋆ R)) → ((⟦P⟧ : SLP α) ⊢ Q ⋆ (⟦P⟧ : SLP α) ⋆ R) := by
  sorry

theorem solve_pure_star_mv {α : Type _} [LawfulHeap α] {P : SLP α} {Q : Prop}
  : Q → ((P : SLP α) ⊢ (⟦Q⟧ : SLP α) ⋆ P) := by
  sorry

theorem apply_exi_star {α β : Type _} [LawfulHeap α]
    {P : β → SLP α} {H R Q : SLP α} {v : β}
  : (H ⊢ R ⋆ P v ⋆ Q) → (H ⊢ (∃∃ v, P v) ⋆ R ⋆ Q) := by
  sorry

theorem apply_exi {α β : Type _} [LawfulHeap α]
    {P : β → SLP α} {H Q : SLP α} {v : β}
  : (H ⊢ P v ⋆ Q) → (H ⊢ (∃∃ v, P v) ⋆ Q) := by
  sorry

theorem star_top_of_star_mvar {α : Type _} [LawfulHeap α] {H Q R : SLP α}
  : (H ⊢ Q ⋆ R) → (H ⊢ Q ⋆ ⊤) := by
  sorry

lemma solve_compose {α : Type _} [LawfulHeap α] {P Q R S : SLP α}
    (h₁ : P ⊢ Q ⋆ R) (h₂ : R ⊢ S) : P ⊢ Q ⋆ S := by
  sorry

lemma solve_compose_with_sinks {α : Type _} [LawfulHeap α]
    {P Q R S T : SLP α}
    (h₁ : P ⊢ Q ⋆ R)
    (h₂ : R ⊢ S ⋆ T)
  : P ⊢ (Q ⋆ S) ⋆ T := by
  sorry

lemma rotate_to_sinks {α : Type _} [LawfulHeap α] {P Q R S : SLP α}
    (h : P ⊢ R ⋆ (Q ⋆ S))
  : P ⊢ (Q ⋆ R) ⋆ S := by
  sorry

theorem ent_congr {p : Prime} {P P' Q Q' : SLP (State p)}
    (h₁ : P = P') (h₂ : Q = Q')
  : (P' ⊢ Q') → (P ⊢ Q) := by
  kan_cases h₁
  kan_cases h₂
  kan_intro x
  kan_exact x

theorem move_to_sinks {p : Prime} {P Q : SLP (State p)}
  : (P ⊢ Q) → (P ⊢ (⟦⟧ ⋆ Q)) := by
  sorry

end Internal

structure SLConfig where
  isUnsafe : Bool

def SLConfig.default : SLConfig := { isUnsafe := false }

instance : Inhabited SLConfig where
  default := SLConfig.default

structure SLGoals where
  entailments : List MVarId
  props : List MVarId
  implicits : List MVarId

abbrev SLM := ReaderT SLConfig TacticM

def SLM.run {α} (x : SLM α) (r : SLConfig) : TacticM α :=
  ReaderT.run x r

instance : MonadBacktrack (Lean.Elab.Tactic.SavedState) SLM where
  saveState := Lean.Elab.Tactic.saveState
  restoreState b := Lean.Elab.Tactic.SavedState.restore b

def SLM.tryCatchRestore {α : Type} (x : SLM α) (h : Exception → SLM α) : SLM α := do
  let s ← saveState
  try x catch ex => s.restore; h ex

instance : MonadExcept Exception SLM where
  throw := throw
  tryCatch := SLM.tryCatchRestore

def SLGoals.flatten (g : SLGoals) : List MVarId := g.entailments ++ g.props ++ g.implicits

instance : Append SLGoals where
  append g₁ g₂ := {
    entailments := g₁.entailments ++ g₂.entailments,
    props := g₁.props ++ g₂.props,
    implicits := g₁.implicits ++ g₂.implicits
  }

instance : Inhabited SLGoals where
  default := { entailments := [], props := [], implicits := [] }

def _root_.Lean.MVarId.apply' (m : MVarId) (e : Lean.Expr) : TacticM (List MVarId) := do
  trace[KanLampe.SL] "Applying {e}"
  m.apply e

lemma dite_lift_lift {R : Prop} [Decidable R] {α : Type _} [LawfulHeap α]
    {P : R → Prop} {Q : ¬R → Prop}
  : (if h : R then (⟦P h⟧ : SLP α) else (⟦Q h⟧ : SLP α))
      = (⟦if h : R then P h else Q h⟧ : SLP α) := by
  sorry

/--
Solves goals of the form `P ⊢ [r ↦ v] ⋆ ?_`.
-/
partial def solveSingletonStarMV (goal : MVarId) (lhs : SLTerm) (rhs : Lean.Expr) : SLM SLGoals :=
    goal.withContext $
    withTraceNode `KanLampe.SL (fun e => return f!"solveSingletonStarMV {Except.emoji e}") $ do
  match lhs with
  | SLTerm.singleton _ v _ =>
    if (←withNewMCtxDepth $ isDefEq v rhs) then
      let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.singleton_congr_star_mv)
        | throwError "unexpect goals in singleton_congr_star_mv"
      let heq ← try heq.refl; pure []
        catch _ => pure [heq]
      pure $ SLGoals.mk [] heq impl
    else throwError "final singleton is not equal"
  | SLTerm.lmbSingleton _ v _ =>
    if (←withNewMCtxDepth $ isDefEq v rhs) then
      let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.lmbSingleton_congr_star_mv)
        | throwError "unexpect goals in lmbSingleton_congr_star_mv"
      let heq ← try heq.refl; pure []
        catch _ => pure [heq]
      pure $ SLGoals.mk [] heq impl
    else throwError "final lmb singleton is not equal"
  | SLTerm.star _ l r =>
    match l with
    | SLTerm.singleton _ v _ => do
      if (←withNewMCtxDepth $ isDefEq v rhs) then
        let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.singleton_congr_star)
          | throwError "unexpect goals in singleton_congr_star"
        let heq ← try heq.refl; pure []
          catch _ => pure [heq]
        pure $ SLGoals.mk [] heq impl
      else
        let hent :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence)
          | throwError "unexpect goals in skip_impure_evidence"
        let goals ← solveSingletonStarMV hent r rhs
        pure $ goals ++ SLGoals.mk [] [] impl
    | SLTerm.lmbSingleton _ v _ => do
      if (←withNewMCtxDepth $ isDefEq v rhs) then
        let heq :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.lmbSingleton_congr_star)
          | throwError "unexpect goals in lmbSingleton_congr_star"
        let heq ← try heq.refl; pure []
          catch _ => pure [heq]
        pure $ SLGoals.mk [] heq impl
      else
        let hent :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence)
          | throwError "unexpect goals in skip_impure_evidence"
        let goals ← solveSingletonStarMV hent r rhs
        pure $ goals ++ SLGoals.mk [] [] impl
    | _ =>
      let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence)
        | throwError "unexpect goals in skip_impure_evidence"
      let goals ← solveSingletonStarMV hEnt r rhs
      pure $ goals ++ SLGoals.mk [] [] impl
  | e => throwError "unrecognized shape in solveSingletonStarMV {e.printShape}"

def solveExactStarMV (goal : MVarId) (lhs : SLTerm) (rhs : Lean.Expr) : SLM SLGoals :=
    withTraceNode `KanLampe.SL (fun e => return f!"solveExactStarMV {Except.emoji e}") do
  let isUnsafe := (←read).isUnsafe
  match lhs with
  | SLTerm.unrecognized expr =>
    let mvarGuard := if isUnsafe then id else withNewMCtxDepth
    if ←mvarGuard $ isDefEq expr rhs then
      let impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.entails_self_true)
      pure $ SLGoals.mk [] [] impl
    else throwError "final unrecognized is not equal"
  | SLTerm.star _ l r => do
    match l with
    | SLTerm.unrecognized expr => do
      let mvarGuard := if isUnsafe then id else withNewMCtxDepth
      if ←mvarGuard $ isDefEq expr rhs then
        let impl ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_self)
        pure $ SLGoals.mk [] [] impl
      else
        let hent :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence)
          | throwError "unexpect goals in skip_impure_evidence"
        let goals ← solveExactStarMV hent r rhs
        pure $ goals ++ SLGoals.mk [] [] impl
    | _ => do
      let hEnt :: impl ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.skip_impure_evidence)
        | throwError "unexpect goals in skip_impure_evidence"
      let goals ← solveExactStarMV hEnt r rhs
      pure $ goals ++ SLGoals.mk [] [] impl
  | _ => throwError "Unrecognized shape in solveExactStarMV"

partial def rewriteSides (goal : MVarId) (newPre newPost : Lean.Expr) (eqPre eqPost : Lean.Expr)
  : SLM MVarId := do
  let newGoalTp ← mkAppM ``SLP.entails #[newPre, newPost]
  let nextGoal ← mkFreshMVarId
  let goalExpr ← mkFreshExprMVarWithId nextGoal (some newGoalTp)
  let congr ← mkAppM ``Internal.ent_congr #[eqPre, eqPost, goalExpr]
  goal.assign congr
  pure nextGoal

partial def normalizePre (goal : MVarId) (pre post : SLTerm) : SLM (SLTerm × MVarId) := do
  let (pre', preEq) ← KanLampe.SL.norm pre
  let postEq ← mkAppM ``Eq.refl #[post.expr]
  let goal ← rewriteSides goal pre'.expr post.expr preEq postEq
  pure (pre', goal)

partial def normalizeSides (goal : MVarId) (pre post : SLTerm)
  : SLM (SLTerm × SLTerm × MVarId) := do
  let (pre', preEq) ← KanLampe.SL.norm pre
  let (post', postEq) ← KanLampe.SL.norm post
  let goal ← rewriteSides goal pre'.expr post'.expr preEq postEq
  pure (pre', post', goal)

partial def solveGoal (goal : MVarId) (pre post : SLTerm) : SLM SLGoals :=
    withTraceNode `KanLampe.SL (tag := "solveGoal") (fun e => return f!"solveGoal {Except.emoji e}") do
  match post with
  | .singleton _ v _ => solveSingletonStarMV goal pre v
  | .lmbSingleton _ v _ => solveSingletonStarMV goal pre v
  | .lift _ =>
    let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_pure_star_mv)
      | throwError "unexpected goals in solve_pure_star_mv"
    pure $ SLGoals.mk [] [g] impls
  | .unit _ =>
    let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_unit_star_mv)
    pure $ SLGoals.mk [] [] impls
  | .unrecognized expr => solveExactStarMV goal pre expr
  | _ => throwError "Unrecognized shape in solveGoal"

partial def solveGoals (goal : MVarId) (pre goals sinks : SLTerm)
  : SLM (SLGoals × SLTerm × SLTerm × MVarId) :=
    withTraceNode `KanLampe.SL (tag := "solveGoals") (fun e => return f!"solveGoals {Except.emoji e}") do
  match goals with
  | .unit _ =>
    trace[KanLampe.SL] "Finished working through goals"
    let [goal] ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.move_to_sinks)
      | throwError "unexpected goals in move_to_sinks"
    let (pre, post, goal) ← normalizeSides goal pre sinks
    pure (default, pre, post, goal)
  | .star _ l r => do
    try
      let itemG :: restG :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_compose_with_sinks)
        | throwError "unexpected goals in solve_compose_with_sinks"
      let goals ← solveGoal itemG pre l
      let restGExpr ← restG.instantiateMVarsInType
      let (pre, post) ← parseEntailment restGExpr
      let (pre, restG) ← normalizePre restG pre post
      let (moreGoals, pre, sinks, goal) ← solveGoals restG pre r sinks
      pure (goals ++ moreGoals ++ SLGoals.mk [] [] impls, pre, sinks, goal)
    catch e =>
      trace[KanLampe.SL] "{crossEmoji} Failed to solve goal: {l.printShape} with message {←e.toMessageData.toString}"
      let [restG] ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.rotate_to_sinks)
        | throwError "unexpected goals in rotate_to_sinks"
      let newSink ← mkAppM ``SLP.star #[l.expr, sinks.expr]
      solveGoals restG pre r (SLTerm.star newSink l sinks)
  | other => do
    try
      let itemG :: restG :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.solve_compose)
        | throwError "unexpected goals in solve_compose"
      let goals ← solveGoal itemG pre other
      let restGExpr ← restG.instantiateMVarsInType
      let (pre, post) ← parseEntailment restGExpr
      let (pre, post, restG) ← normalizeSides restG pre post
      pure (goals ++ SLGoals.mk [] [] impls, pre, post, restG)
    catch e =>
      trace[KanLampe.SL] "{crossEmoji} Failed to solve goal: {other.printShape} with message {←e.toMessageData.toString}"
      let gExpr ← goal.instantiateMVarsInType
      let (pre, post) ← parseEntailment gExpr
      let (pre, post, goal) ← normalizeSides goal pre post
      trace[KanLampe.SL] "Reparsed goal: {←ppExpr pre.expr} ⊢ ({←ppExpr post.expr})"
      pure (default, pre, post, goal)

partial def doPullWith (pre : SLTerm) (goal : MVarId) (puller finalPuller : Lean.Expr)
  : SLM (MVarId × List MVarId) := goal.withContext $ do
  match pre with
  | .star _ (.lift _) r =>
    let goal :: impls ← goal.apply' puller | throwError "unexpected goals in doPullWith"
    let (fv, goal) ← goal.intro1
    trace[KanLampe.SL] "Pulled out: {fv.name}"
    let (g, gs) ← doPullWith r goal puller finalPuller
    pure (g, impls ++ gs)
  | .lift _ =>
    let goal :: impls ← goal.apply' finalPuller | throwError "unexpected goals in doPullWith"
    let (_, goal) ← goal.intro1
    pure (goal, impls)
  | _ => pure (goal, [])

partial def pullPures (goal : MVarId) (pre post : SLTerm) : SLM (MVarId × List MVarId) :=
    goal.withContext $
    withTraceNode `KanLampe.SL (tag := "pullPures") (fun e => return f!"pullPures {Except.emoji e}") do
  let (goal, puller, finalPuller) ← if post.hasMVars then
    let (p, pmv, postEqMVars) ← KanLampe.SL.split_by (fun t => match t with
      | SLTerm.mvar _ => pure .right
      | _ => pure .left
    ) post
    match pmv with
    | .mvar _ => pure ()
    | _ => throwError "unexpected result in pullPures"
    let newPost ← mkAppM ``SLP.star #[p.expr, pmv.expr]
    let preEq ← mkAppM ``Eq.refl #[pre.expr]
    let goal ← rewriteSides goal pre.expr newPost preEq postEqMVars
    pure (goal,
      ←mkConstWithFreshMVarLevels ``Internal.skip_pure_evidence,
      ←mkConstWithFreshMVarLevels ``Internal.skip_final_pure_evidence)
  else
    pure (goal,
      ←mkConstWithFreshMVarLevels ``KanLampe.SLP.pure_left,
      ←mkConstWithFreshMVarLevels ``KanLampe.SLP.pure_left')
  doPullWith pre goal puller finalPuller

partial def doApplyExis (goal : MVarId) (postExis : SLTerm) : SLM (MVarId × List MVarId) := do
  match postExis with
  | SLTerm.exi _ _ =>
    let goal :: goals ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.apply_exi)
      | throwError "unexpected goals in apply_exi"
    pure (goal, goals)
  | SLTerm.star _ _ r => do
    let goal :: goals ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.apply_exi_star)
      | throwError "unexpected goals in apply_exi_star"
    let (goal, g₂) ← doApplyExis goal r
    pure (goal, goals ++ g₂)
  | _ => pure (goal, [])

partial def applyExis (goal : MVarId) (pre post : SLTerm) : SLM (MVarId × List MVarId) :=
    goal.withContext do
  let (p, pmv, postEqMVars) ← KanLampe.SL.split_by (fun t => match t with
    | SLTerm.exi _ _ => pure .left
    | _ => pure .right
  ) post
  let newPost ← mkAppM ``SLP.star #[p.expr, pmv.expr]
  let preEq ← mkAppM ``Eq.refl #[pre.expr]
  let goal ← rewriteSides goal pre.expr newPost preEq postEqMVars
  doApplyExis goal p

partial def solveSinks (goal : MVarId) (pre post : SLTerm) : SLM SLGoals :=
    goal.withContext $
    withTraceNode `KanLampe.SL (tag := "solveSinks") (fun e => return f!"solveSinks {Except.emoji e}") do
  trace[KanLampe.SL] "Current goal: {←ppExpr pre.expr} ⊢ ({←ppExpr post.expr})"
  match post with
  | .mvar _ =>
    let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_self)
    return SLGoals.mk [] [] impls
  | .top _ =>
    let impls ← goal.apply' (←mkConstWithFreshMVarLevels ``SLP.entails_top)
    return SLGoals.mk [] [] impls
  | _ => pure $ SLGoals.mk [goal] [] []

partial def pullExisLoop (goal : MVarId) : SLM (MVarId × List MVarId) := goal.withContext do
  let tp ← goal.instantiateMVarsInType
  let (l, _) ← parseEntailment tp
  match l with
  | .exi _ _ =>
    let goal :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.shift_exists_to_mvar)
      | throwError "unexpected goals in shift_exists_to_mvar"
    goal.withContext do
      let (_, goal) ← goal.intro1
      let (r, rs) ← pullExisLoop goal
      pure $ (r, impls ++ rs)
  | _ => pure (goal, [])

partial def pullExis (pre post : SLTerm) (goal : MVarId) : SLM (MVarId × List MVarId) :=
    goal.withContext do
  let (goals, sink, postEq) ← KanLampe.SL.split_by (fun t => match t with
  | SLTerm.mvar _ => pure .right
  | SLTerm.top _ => pure .right
  | _ => pure .left
  ) post
  let newPost ← mkAppM ``SLP.star #[goals.expr, sink.expr]
  let (pre, preEq) ← KanLampe.SL.surfaceExis pre
  let goal ← rewriteSides goal pre newPost preEq postEq
  let (goal, impls) ← match sink with
  | .mvar _ => pure (goal, [])
  | .top _ =>
    let g :: impls ← goal.apply' (←mkConstWithFreshMVarLevels ``Internal.star_top_of_star_mvar)
      | throwError "unexpected goals in star_top_of_star_mvar"
    pure (g, impls)
  | _ => throwError "unsupported sink shape"
  let (g, r) ← pullExisLoop goal
  pure (g, r ++ impls)

partial def parseAndNormalizeEntailment (goal : MVarId) : SLM (SLTerm × SLTerm × MVarId) :=
    goal.withContext do
  let target ← goal.instantiateMVarsInType
  let (pre, post) ← parseEntailment target
  let (pre, post, goal) ← normalizeSides goal pre post
  return (pre, post, goal)

/--
Solves an entailment of the form `P ⊢ Q ⋆ ⊤` or `P ⊢ Q ⋆ ?M`.
-/
partial def solveEntailment' (goal : MVarId) : SLM SLGoals :=
    goal.withContext $
    withTraceNode `KanLampe.SL (tag := "solveEntailment") (fun e => return f!"solveEntailment {Except.emoji e}") do
  let (pre, post, goal) ← parseAndNormalizeEntailment goal
  let safety := if (←read).isUnsafe then " (unsafe)" else ""
  trace[KanLampe.SL] "Initial goal{safety}: {←ppExpr pre.expr} ⊢ ({←ppExpr post.expr})"
  let (goal, impls₁) ← pullExis pre post goal
  let (pre, post, goal) ← parseAndNormalizeEntailment goal
  let (goal, impls₂) ← pullPures goal pre post
  let (pre, post, goal) ← parseAndNormalizeEntailment goal

  let (goal, exiGoals) ← applyExis goal pre post

  goal.withContext do
    let target ← goal.instantiateMVarsInType
    let (pre, post) ← parseEntailment target
    let (pre, preEq) ← KanLampe.SL.norm pre
    let (post, postEq) ← KanLampe.SL.norm post
    let (goals, sinks, postEqSplit) ← KanLampe.SL.split_by (fun t => match t with
      | SLTerm.mvar _ => pure .right
      | SLTerm.top _ => pure .right
      | _ => pure .left
    ) post
    let postExpr ← mkAppM ``SLP.star #[goals.expr, sinks.expr]
    let postEqTotal ← mkAppM ``Eq.trans #[postEq, postEqSplit]
    let goal ← rewriteSides goal pre.expr postExpr preEq postEqTotal

    trace[KanLampe.SL] "Current goal: {←ppExpr pre.expr} ⊢ ({←ppExpr goals.expr}) ⋆ ({←ppExpr sinks.expr})"

    let (moreGoals, pre, post, goal) ← solveGoals goal pre goals sinks
    let res ← solveSinks goal pre post
    pure $ res ++ moreGoals ++ SLGoals.mk [] exiGoals (impls₁ ++ impls₂)

/--
Solves an entailment of the form `P ⊢ Q ⋆ ⊤` or `P ⊢ Q ⋆ ?M`.
-/
partial def solveEntailment (goal : MVarId) (config : SLConfig) : TacticM SLGoals :=
  SLM.run (solveEntailment' goal) config

/--
Solves separation logic entailments of the form `P ⊢ Q ⋆ ⊤` or `P ⊢ Q ⋆ ?M`.
-/
elab "sl" m:"unsafe"? : tactic => do
  let config : SLConfig := ⟨m.isSome⟩
  let target ← getMainGoal
  let newGoals ← solveEntailment target config
  replaceMainGoal newGoals.flatten

end KanLampe.SL
