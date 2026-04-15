import KanLampe.Ast.Extensions
import KanLampe.Hoare.Builtins
import KanLampe.Hoare.SepTotal
import KanLampe.SeparationLogic.State
import KanLampe.Tactic.EnvSubsetSolver
import KanLampe.Tactic.SL
import KanLampe.Tactic.SL.Term
import KanLampe.Tactic.Traits

import Lean.Meta.Tactic.Simp.Main

/-!
# KanLampe.Tactic.Steps

Port of `Lampe.Tactic.Steps`.  Provides the main `steps`, `step_as`,
`loop_inv`, `enter_decl`, `enter_lambda_as`, and `steps_named`
tactics used to drive Hoare-style program proofs.

Proofs here are minimal; several supporting lemmas are left as
`sorry` pending the port of the upstream builtin intro lemmas.  The
metaprogramming pipeline follows the upstream structure verbatim
with namespaces and trace classes renamed to `KanLampe`.
-/

open KanLampe
open KanLampe.SL

open Lean Elab.Tactic Parser.Tactic Lean.Meta Qq KanLampe.STHoare

namespace KanLampe.Steps

initialize
  Lean.registerTraceClass `KanLampe.STHoare.Helpers

def parseTriple (e : Lean.Expr) : TacticM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  if e.isAppOf' ``STHoare then
    let args := e.getAppArgs'
    return some (args[3]!, args[4]!, args[5]!)
  else return none

def isLetIn (e : Lean.Expr) : Bool := e.isAppOf' ``KanLampe.Expr.letIn

def getLetInVarName (e : Lean.Expr) : TacticM (Option Name) := do
  let args := Lean.Expr.getAppArgs' e
  let body := args[4]!
  match body with
  | Lean.Expr.lam n _ _ _ => return some n
  | _ => return none

/--
Attempts to get a term that can close the goal.
-/
def getClosingTerm (val : Lean.Expr) : TacticM (Option (TSyntax `term)) :=
    withTraceNode `KanLampe.STHoare.Helpers (fun e => return f!"getClosingTerm {Except.emoji e}") do
  let head := val.getAppFn'
  match head with
  | Lean.Expr.const n _ =>
    match n with
    | ``KanLampe.Expr.skip => return some (←``(skip_intro))
    | ``KanLampe.Expr.var => return some (←``(var_intro))
    | ``KanLampe.Expr.constU => return some (←``(constU_intro))
    | ``KanLampe.Expr.constFp => return some (←``(constFp_intro))
    | ``KanLampe.Expr.lam => return some (←``(lam_intro))
    | ``KanLampe.Expr.mkTuple => return some (←``(genericTotalPureBuiltin_intro (a := (_,_)) Builtin.mkTuple rfl))
    | ``KanLampe.Expr.mkArray =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkArray"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray (a := ($size, _)) rfl))
    | ``KanLampe.Expr.mkRepArray =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkArray"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray (a := ($size, _)) rfl))
    | ``KanLampe.Expr.mkVector =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkVector"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkVector (a := ($size, _)) rfl))
    | ``KanLampe.Expr.mkRepVector =>
      let some size := val.getAppArgs[2]? | throwError "malformed mkVector"
      let size ← size.toSyntax
      return some (←``(genericTotalPureBuiltin_intro Builtin.mkVector (a := ($size, _)) rfl))
    | ``KanLampe.Expr.getLens => return some (←``(getLens_intro))
    | ``KanLampe.Expr.modifyLens => return some (←``(modifyLens_intro))
    | ``KanLampe.Expr.getMember => return some (← ``(genericTotalPureBuiltin_intro (Builtin.getMember _) rfl))
    | ``KanLampe.Expr.fn => return some (←``(fn_intro))
    | ``KanLampe.Expr.callBuiltin =>
      let some builtin := val.getAppArgs[3]? | throwError "malformed builtin"
      let builtinName := builtin.getAppFn
      match builtinName with
      | Lean.Expr.const n _ =>
        match n with
        | ``KanLampe.Builtin.fresh => return some (←``(fresh_intro))
        | ``KanLampe.Builtin.assert => return some (←``(assert_intro))
        | ``KanLampe.Builtin.staticAssert => return some (←``(staticAssert_intro))

        | ``KanLampe.Builtin.bNot => return some (←``(genericTotalPureBuiltin_intro Builtin.bNot (a := ()) rfl))
        | ``KanLampe.Builtin.bAnd => return some (←``(genericTotalPureBuiltin_intro Builtin.bAnd rfl))
        | ``KanLampe.Builtin.bXor => return some (←``(genericTotalPureBuiltin_intro Builtin.bXor rfl))
        | ``KanLampe.Builtin.bOr  => return some (←``(genericTotalPureBuiltin_intro Builtin.bOr  rfl))
        | ``KanLampe.Builtin.bEq  => return some (←``(genericTotalPureBuiltin_intro Builtin.bEq  rfl))

        | ``KanLampe.Builtin.uNot => return some (←``(genericTotalPureBuiltin_intro Builtin.uNot rfl))
        | ``KanLampe.Builtin.uAnd => return some (←``(genericTotalPureBuiltin_intro Builtin.uAnd rfl))
        | ``KanLampe.Builtin.uOr => return some (←``(genericTotalPureBuiltin_intro Builtin.uOr rfl))
        | ``KanLampe.Builtin.uXor => return some (←``(genericTotalPureBuiltin_intro Builtin.uXor rfl))
        | ``KanLampe.Builtin.uShl => return some (←``(genericTotalPureBuiltin_intro Builtin.uShl rfl))
        | ``KanLampe.Builtin.uShr => return some (←``(genericTotalPureBuiltin_intro Builtin.uShr rfl))

        | ``KanLampe.Builtin.iNot => return some (←``(genericTotalPureBuiltin_intro Builtin.iNot rfl))
        | ``KanLampe.Builtin.iAnd => return some (←``(genericTotalPureBuiltin_intro Builtin.iAnd rfl))
        | ``KanLampe.Builtin.iOr => return some (←``(genericTotalPureBuiltin_intro Builtin.iOr rfl))
        | ``KanLampe.Builtin.iXor => return some (←``(genericTotalPureBuiltin_intro Builtin.iXor rfl))
        | ``KanLampe.Builtin.iShl => return some (←``(iShl_intro))
        | ``KanLampe.Builtin.iShr => return some (←``(iShr_intro))

        | ``KanLampe.Builtin.cast => return some (←``(cast_intro))

        | ``KanLampe.Builtin.fAdd => return some (←``(genericTotalPureBuiltin_intro Builtin.fAdd rfl (a := ())))
        | ``KanLampe.Builtin.fMul => return some (←``(genericTotalPureBuiltin_intro Builtin.fMul rfl (a := ())))
        | ``KanLampe.Builtin.fSub => return some (←``(genericTotalPureBuiltin_intro Builtin.fSub rfl (a := ())))
        | ``KanLampe.Builtin.fNeg => return some (←``(genericTotalPureBuiltin_intro Builtin.fNeg rfl (a := ())))
        | ``KanLampe.Builtin.fDiv => return some (←``(fDiv_intro))

        | ``KanLampe.Builtin.fEq => return some (←``(genericTotalPureBuiltin_intro Builtin.fEq rfl (a := ())))
        | ``KanLampe.Builtin.uEq => return some (←``(genericTotalPureBuiltin_intro Builtin.uEq rfl))
        | ``KanLampe.Builtin.iEq => return some (←``(genericTotalPureBuiltin_intro Builtin.iEq rfl))

        | ``KanLampe.Builtin.fNeq => return some (←``(genericTotalPureBuiltin_intro Builtin.fNeq rfl))
        | ``KanLampe.Builtin.uNeq => return some (←``(genericTotalPureBuiltin_intro Builtin.uNeq rfl))
        | ``KanLampe.Builtin.iNeq => return some (←``(genericTotalPureBuiltin_intro Builtin.iNeq rfl))

        | ``KanLampe.Builtin.iGt => return some (←``(genericTotalPureBuiltin_intro Builtin.iGt rfl))
        | ``KanLampe.Builtin.iLt => return some (←``(genericTotalPureBuiltin_intro Builtin.iLt rfl))
        | ``KanLampe.Builtin.uGt => return some (←``(genericTotalPureBuiltin_intro Builtin.uGt rfl))
        | ``KanLampe.Builtin.uLt => return some (←``(genericTotalPureBuiltin_intro Builtin.uLt rfl))

        | ``KanLampe.Builtin.uAdd => return some (←``(uAdd_intro))
        | ``KanLampe.Builtin.uMul => return some (←``(uMul_intro))
        | ``KanLampe.Builtin.uDiv => return some (←``(uDiv_intro))
        | ``KanLampe.Builtin.uSub => return some (←``(uSub_intro))
        | ``KanLampe.Builtin.uRem => return some (←``(uRem_intro))
        | ``KanLampe.Builtin.uLeq => return some (←``(uLeq_intro))

        | ``KanLampe.Builtin.iAdd => return some (←``(iAdd_intro))
        | ``KanLampe.Builtin.iMul => return some (←``(iMul_intro))
        | ``KanLampe.Builtin.iDiv => return some (←``(iDiv_intro))
        | ``KanLampe.Builtin.iSub => return some (←``(iSub_intro))
        | ``KanLampe.Builtin.iRem => return some (←``(iRem_intro))
        | ``KanLampe.Builtin.iNeg => return some (←``(iNeg_intro))

        | ``KanLampe.Builtin.modulusLeBits => return some (←``(genericTotalPureBuiltin_intro Builtin.modulusLeBits (a := ()) rfl))
        | ``KanLampe.Builtin.modulusBeBits => return some (←``(genericTotalPureBuiltin_intro Builtin.modulusBeBits (a := ()) rfl))
        | ``KanLampe.Builtin.modulusLeBytes => return some (←``(genericTotalPureBuiltin_intro Builtin.modulusLeBytes (a := ()) rfl))
        | ``KanLampe.Builtin.modulusBeBytes => return some (←``(genericTotalPureBuiltin_intro Builtin.modulusBeBytes (a := ()) rfl))
        | ``KanLampe.Builtin.modulusNumBits => return some (←``(genericTotalPureBuiltin_intro Builtin.modulusNumBits (a := ()) rfl))

        | ``KanLampe.Builtin.strAsBytes => return some (←``(strAsBytes_intro))
        | ``KanLampe.Builtin.arrayAsStrUnchecked => return some (←``(arrayAsStrUnchecked_intro))

        | ``KanLampe.Builtin.isUnconstrained =>
          return some (←``(genericTotalPureBuiltin_intro Builtin.isUnconstrained rfl))

        -- Array builtins
        | ``KanLampe.Builtin.mkArray =>
          let some argTypes := val.getAppArgs[1]? | throwError "malformed mkArray"
          let argTypes ← argTypes.toSyntax
          return some (←``(genericTotalPureBuiltin_intro Builtin.mkArray (a := (List.length $argTypes, _)) rfl))
        | ``KanLampe.Builtin.mkRepeatedArray =>
          return some (←``(genericTotalPureBuiltin_intro Builtin.mkRepeatedArray (a := (_, _)) rfl))
        | ``KanLampe.Builtin.arrayIndex => return some (←``(arrayIndex_intro))
        | ``KanLampe.Builtin.arrayLen =>
          let some argTps :=  val.getAppArgs[1]? | throwError "malformed arrayLen"
          let some (_, argTps) := argTps.listLit? | throwError "malformed arrayLen"
          let some argTp := argTps.head? | throwError "malformed arrayLen"
          match_expr argTp with
          | Tp.vector _ => return some (←``(vector_arrayLen_intro))
          | Tp.array _ _ => return some (←``(array_arrayLen_intro))
          | _ => return none
        | ``KanLampe.Builtin.asVector => return some (←``(genericTotalPureBuiltin_intro Builtin.asVector (a := (_,_)) rfl))

        -- Vector builtins
        | ``KanLampe.Builtin.mkVector =>
          let some argTypes := val.getAppArgs[1]? | throwError "malformed mkVector"
          let argTypes ← argTypes.toSyntax
          return some (←``(genericTotalPureBuiltin_intro Builtin.mkVector (a := (List.length $argTypes, _)) rfl))
        | ``KanLampe.Builtin.mkRepeatedVector =>
          return some (←``(genericTotalPureBuiltin_intro Builtin.mkRepeatedVector (a := _) rfl))
        | ``KanLampe.Builtin.vectorPushBack => return some (←``(genericTotalPureBuiltin_intro Builtin.vectorPushBack rfl))
        | ``KanLampe.Builtin.vectorPushFront => return some (←``(genericTotalPureBuiltin_intro Builtin.vectorPushFront rfl))
        | ``KanLampe.Builtin.vectorIndex => return some (←``(vectorIndex_intro))
        | ``KanLampe.Builtin.ref => return some (←``(ref_intro))
        | ``KanLampe.Builtin.readRef => return some (←``(readRef_intro))

        -- Field builtins
        | ``KanLampe.Builtin.applyRangeConstraint => return some (←``(applyRangeConstraint_intro))
        | ``KanLampe.Builtin.fModBeBits => return some (←``(genericTotalPureBuiltin_intro Builtin.fModBeBits rfl))
        | ``KanLampe.Builtin.fModBeBytes => return some (←``(genericTotalPureBuiltin_intro Builtin.fModBeBytes rfl))
        | ``KanLampe.Builtin.fModLeBits => return some (←``(genericTotalPureBuiltin_intro Builtin.fModLeBits rfl))
        | ``KanLampe.Builtin.fModLeBytes => return some (←``(genericTotalPureBuiltin_intro Builtin.fModLeBytes rfl))
        | ``KanLampe.Builtin.fModNumBits => return some (←``(fModNumBits_intro))
        | ``KanLampe.Builtin.iAsField => return some (←``(genericTotalPureBuiltin_intro Builtin.iAsField rfl))
        | ``KanLampe.Builtin.iFromField => return some (←``(genericTotalPureBuiltin_intro Builtin.iFromField rfl))
        | ``KanLampe.Builtin.uAsField => return some (←``(genericTotalPureBuiltin_intro Builtin.uAsField rfl))
        | ``KanLampe.Builtin.uFromField => return some (←``(genericTotalPureBuiltin_intro Builtin.uFromField rfl))
        | ``KanLampe.Builtin.toLeBits => return some (←``(toLeBits_intro))
        | ``KanLampe.Builtin.toBeBits => return some (←``(toBeBits_intro))
        | ``KanLampe.Builtin.toLeRadix => return some (←``(toLeRadix_intro))
        | ``KanLampe.Builtin.toBeRadix => return some (←``(toBeRadix_intro))

        -- Tuple/struct builtins
        | ``KanLampe.Builtin.makeData => return some (← ``(genericTotalPureBuiltin_intro (a := (_, _)) Builtin.makeData rfl))
        | ``KanLampe.Builtin.getMember => return some (← ``(genericTotalPureBuiltin_intro (Builtin.getMember _) rfl))

        | ``KanLampe.Builtin.zeroed => return some (←``(genericTotalPureBuiltin_intro Builtin.zeroed rfl))


        | _ => return none
      | _ => return none
    | ``KanLampe.Expr.ref => return some (←``(ref_intro))
    | ``KanLampe.Expr.readRef => return some (←``(readRef_intro))
    | ``KanLampe.Expr.litNum =>
      let some vtp := val.getAppArgs[1]? | throwError "malformed litNum"
      let  Lean.Expr.const vtp _ := vtp.getAppFn | throwError "malformed litNum"
      match vtp with
      | ``Tp.field => return some (←``(litField_intro))
      | ``Tp.u => return some (←``(litU_intro))
      | ``Tp.i => return some (←``(litI_intro))
      | ``Tp.bool =>
        let some v := val.getAppArgs[2]? | throwError "malformed litNum"
        let some (v : Lean.Expr) := v.getAppArgs[1]? | throwError "malformed litNum"
        trace[KanLampe.STHoare.Helpers] "litNum bool {v}"
        match v.natLit! with
        | 0 => return some (←``(litFalse_intro))
        | 1 => return some (←``(litTrue_intro))
        | _ => return none
      | _ => return none
    | ``KanLampe.Expr.litStr => return some (←``(litStr_intro))
    | _ => return none

  | _ => pure none

def getLetInHeadClosingTheorem (e : Lean.Expr) : TacticM (Option (TSyntax `term)) := do
  let args := Lean.Expr.getAppArgs e
  let some val := args[3]? | throwError "malformed letIn"
  getClosingTerm val

structure AddLemma where
  expr : Lean.Expr
  term : Term
  /--
  Controls whether the environment is generalized before applying the lemma.
  -/
  generalizeEnv : Bool := false

def tryApplySyntaxes (goal : MVarId) (lemmas : List AddLemma): TacticM (List MVarId) := match lemmas with
| [] => throwError "no lemmas left"
| n::ns => do
  trace[KanLampe.STHoare.Helpers] "trying {←ppExpr n.expr} with generalizeEnv: {n.generalizeEnv}"
  try
    let (subset, goal, others) ← if n.generalizeEnv
      then
        let subset :: main :: others ← evalTacticAt (←`(tactic|apply KanLampe.STHoare.is_mono)) goal
          | throwError "apply KanLampe.STHoare.is_mono gave unexpected result"
        pure ([subset], main, others)
      else pure ([], goal, [])
    let main ← evalTacticAt (←`(tactic|with_unfolding_all apply $(n.term))) goal
    for s in subset do
      trace[KanLampe.STHoare.Helpers] "Solving env subset goal {s}"
      KanLampe.Env.SubsetSolver.solveSubset s
    pure $ main ++ others
  catch e =>
    trace[KanLampe.STHoare.Helpers] "failed {←ppExpr n.expr} with {e.toMessageData}"
    tryApplySyntaxes goal ns

structure TripleGoals where
  triple : Option MVarId
  entailments : List MVarId
  props : List MVarId
  implicits : List MVarId

instance : HAppend TripleGoals SLGoals TripleGoals where
  hAppend g₁ g₂ := ⟨g₁.triple, g₁.entailments ++ g₂.entailments, g₁.props ++ g₂.props, g₁.implicits ++ g₂.implicits⟩

instance : HAppend SLGoals TripleGoals TripleGoals where
  hAppend g₁ g₂ := ⟨g₂.triple, g₁.entailments ++ g₂.entailments, g₁.props ++ g₂.props, g₁.implicits ++ g₂.implicits⟩

instance : Coe SLGoals TripleGoals := ⟨fun g => ⟨none, g.entailments, g.props, g.implicits⟩⟩

def TripleGoals.flatten (g : TripleGoals) : List MVarId :=  g.entailments ++ g.props ++ g.implicits ++ g.triple.toList

lemma SLP.pure_star_iff_and {α : Type _} [LawfulHeap α] {P : Prop} {H : SLP α} {st : α}
    : (⟦P⟧ ⋆ H) st ↔ P ∧ H st := by
  sorry

lemma pluck_pures_destructively {p : Prime} {Γ : Env} {P : Prop}
    {H : SLP (State p)} {tp : Tp} {e : Expr (Tp.denote p) tp}
    {Q : Tp.denote p tp → SLP (State p)}
  : (P → STHoare p Γ H e Q) → (STHoare p Γ (⟦P⟧ ⋆ H) e Q) := by
  sorry

lemma pluck_final_pure_destructively {p : Prime} {Γ : Env} {P : Prop}
    {tp : Tp} {e : Expr (Tp.denote p) tp}
    {Q : Tp.denote p tp → SLP (State p)}
  : (P → STHoare p Γ ⟦True⟧ e Q) → (STHoare p Γ ⟦P⟧ e Q) := by
  sorry

theorem pre_congr {p : Prime} {P₁ P₂ : SLP (State p)} (h : P₁ = P₂)
    {Γ : Env} {α : Tp} {Q : Tp.denote p α → SLP (State p)}
    {e : Expr (Tp.denote p) α}
  : (STHoare p Γ P₂ e Q) → (STHoare p Γ P₁ e Q) := by
  kan_cases h
  kan_intro x
  kan_exact x

partial def rewritePre (goal : MVarId) (eq : Lean.Expr) : TacticM (MVarId × List MVarId) := goal.withContext do
  let thm ← mkAppM ``pre_congr #[eq]
  let goal :: goals ← goal.apply thm | throwError "unexpected goals in pre_congr"
  pure (goal, goals)

partial def introPure (goal : MVarId) : TacticM (MVarId) := goal.withContext $
    withTraceNode `KanLampe.STHoare.Helpers (fun e => return f!"introPure {Except.emoji e}") do
  let (hpFv, goal) ← goal.intro1
  goal.withContext do
    let fvTp ← hpFv.getType
    let fvTp ← instantiateMVars fvTp
    if fvTp.isAppOf' ``Eq then
      trace[KanLampe.STHoare.Helpers] "hp is an equality"
      let args := fvTp.getAppArgs'
      let (lhs : Lean.Expr) ← liftOption args[1]?
      match lhs with
      | .fvar fvid =>
        let name ← fvid.getUserName
        let isInternal := name.toString (escape := false) |>.startsWith "#"
        trace[KanLampe.STHoare.Helpers] "hp is an equality of fvar {name} {isInternal}"
        if isInternal then
          try
            pure (←substCore goal hpFv (symm := false) (tryToSkip := true)).2
          catch _ => pure goal
        else pure goal
      | _ => pure goal
    else
      trace[KanLampe.STHoare.Helpers] "hp is not an equality, it's {fvTp.getAppFn'}"
      pure goal

partial def doPlucks (goal : MVarId) (pre : SLTerm) : TacticM (MVarId × List MVarId) := goal.withContext do
  match pre with
  | .star _ (.lift _) r =>
    let plucker ← mkConstWithFreshMVarLevels ``pluck_pures_destructively
    let goal :: impls₁ ← goal.apply plucker | throwError "unexpected goals in pluck_pures_destructively"
    let goal ← introPure goal
    let (goal, impls₂) ← doPlucks goal r
    pure (goal, impls₁ ++ impls₂)
  | .lift _ =>
    let plucker ← mkConstWithFreshMVarLevels ``pluck_final_pure_destructively
    let goal :: impls₁ ← goal.apply plucker | throwError "unexpected goals in pluck_final_pure_destructively"
    let goal ← introPure goal
    pure (goal, impls₁)
  | _ => return (goal, [])

partial def pluckPures (goal : MVarId) : TacticM (MVarId × List MVarId) := goal.withContext do
  let tgt ← goal.instantiateMVarsInType
  let some (pre, _, _) ← parseTriple tgt | throwError "malformed triple"
  let pre ← parseSLExpr pre
  let (pre, preEq) ← KanLampe.SL.norm pre
  let (goal, impls₁) ← rewritePre goal preEq
  let (goal, impls₂) ← doPlucks goal pre
  pure (goal, impls₁ ++ impls₂)

lemma pull_exi {α : Type _} {p : Prime} {Γ : Env} {P : α → SLP (State p)}
    {tp : Tp} {e : Expr (Tp.denote p) tp}
    {Q : Tp.denote p tp → SLP (State p)}
  : (∀ v, STHoare p Γ (P v) e Q) → STHoare p Γ (∃∃ v, P v) e Q := by
  sorry

partial def doPluckExis (goal : MVarId) : TacticM (MVarId × List MVarId) := goal.withContext do
  let tgt ← goal.instantiateMVarsInType
  let some (pre, _, _) ← parseTriple tgt | throwError "malformed triple"
  let pre ← parseSLExpr pre
  match pre with
  | .exi _ _ =>
    let puller ← mkConstWithFreshMVarLevels ``pull_exi
    let goal :: impls ← goal.apply puller | throwError "unexpected goals in pull_exi"
    goal.withContext do
      let (_, goal) ← goal.intro1
      let (goal, impls₂) ← doPluckExis goal
      pure (goal, impls ++ impls₂)
  | _ => pure (goal, [])

partial def pluckExis (goal : MVarId) : TacticM (MVarId × List MVarId) := goal.withContext do
  let tgt ← goal.instantiateMVarsInType
  let some (pre, _, _) ← parseTriple tgt | throwError "malformed triple"
  let pre ← parseSLExpr pre
  let (_, preEq) ← KanLampe.SL.surfaceExis pre
  let (goal, impls₁) ← rewritePre goal preEq
  let (goal, impls₂) ← doPluckExis goal
  pure (goal, impls₁ ++ impls₂)

partial def simpOnlyGoal (goal : MVarId) : TacticM MVarId := do
  let ctx ← Simp.Context.ofNames (config := { failIfUnchanged := false}) (simpOnly := true)
  let r ← simpGoal goal ctx
  match r.1 with
  | some (_, goal) => return goal
  | none => return goal

def normalizeGoals (goals : TripleGoals) : TacticM TripleGoals :=
    withTraceNode `KanLampe.STHoare.Helpers (fun e => return f!"normalizeGoals {Except.emoji e}") $ do
  match goals with
  | .mk (some trp) ents ps is =>
    let trp ← simpOnlyGoal trp
    let (trp, impls₁) ← pluckExis trp
    let (trp, impls₂) ← pluckPures trp
    return TripleGoals.mk trp ents ps (impls₁ ++ impls₂ ++ is)
  | r => return r

syntax "triple_norm" : tactic
elab "triple_norm" : tactic => do
  let goals ← getMainGoal
  let goals ← normalizeGoals $ TripleGoals.mk goals [] [] []
  replaceMainGoal goals.flatten

/--
Takes a single "obvious" step to attempt to advance the proof state.
-/
partial def step
    (mvar : MVarId)
    (addLemmas : List AddLemma)
    (unsafeUnifySL : Bool)
  : TacticM TripleGoals := mvar.withContext $
    withTraceNode `KanLampe.STHoare.Helpers (fun e => return f!"step {Except.emoji e}") $ do
  let target ← mvar.instantiateMVarsInType
  let some (_, body, _) ← parseTriple target | throwError "not a triple"
  if isLetIn body then
    let closer ← getLetInHeadClosingTheorem body
    let vname ← getLetInVarName body
    trace[KanLampe.STHoare.Helpers] "letIn {closer} {vname}"
    let closer := match closer with
    | some cl => fun goal => do evalTacticAt (←`(tactic|apply $cl)) goal
    | none => fun goal => tryApplySyntaxes goal addLemmas
    let hHead :: hNext :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``letIn_intro) | throwError "bad application"
    let (_, hNext) ← hNext.intro (vname.getD `v)
    let hHead :: hEnt :: impls₂ ← hHead.apply (←mkConstWithFreshMVarLevels ``consequence_frame_left) | throwError "bad application"
    let impls₃ ← closer hHead
    let rEnt ← solveEntailment hEnt ⟨unsafeUnifySL⟩
    return TripleGoals.mk hNext [] [] (impls₁ ++ impls₂ ++ impls₃) ++ rEnt
  else
    let closer ← getClosingTerm body
    let closer := match closer with
    | some cl => fun goal => do evalTacticAt (←`(tactic|apply $cl)) goal
    | none => fun goal => tryApplySyntaxes goal addLemmas
    let hHoare :: hEnt :: qEnt :: impls₁ ← mvar.apply (←mkConstWithFreshMVarLevels ``STHoare.consequence_frame) | throwError "ramified_frame_top failed"
    let impls₂ ← closer hHoare
    let rEnt ← solveEntailment hEnt ⟨unsafeUnifySL⟩
    let (_, qEnt) ← qEnt.intro1
    let qEnt ← if rEnt.entailments.isEmpty then
      solveEntailment qEnt ⟨unsafeUnifySL⟩
    else
      pure $ SLGoals.mk [qEnt] [] []
    return TripleGoals.mk none [] [] (impls₁ ++ impls₂) ++ rEnt ++ qEnt

/--
Takes `limit` obvious steps, behaving like `repeat step`.
-/
partial def stepsLoop
    (goals : TripleGoals)
    (addLemmas : List AddLemma)
    (limit : Nat)
    (strict : Bool := false)
    (unsafeUnifySL : Bool := false)
  : TacticM TripleGoals :=
    withTraceNode `KanLampe.STHoare.Helpers (fun e => return f!"stepsLoop {Except.emoji e}") $ do
  let goals ← normalizeGoals goals
  if limit == 0 then return goals

  match goals.triple with
  | some mvar =>
    let nextTriple ← try some <$> step mvar addLemmas unsafeUnifySL catch e =>
      trace[KanLampe.STHoare.Helpers] "step failed with: {←e.toMessageData.toString}"
      if strict then throw e else pure none
    match nextTriple with
    | some nextTriple => do
      if !nextTriple.entailments.isEmpty then
       return nextTriple ++ SLGoals.mk goals.entailments goals.props goals.implicits
      else
        let nextGoals := nextTriple ++ SLGoals.mk goals.entailments goals.props goals.implicits
        stepsLoop nextGoals addLemmas (limit - 1)
    | none => return goals
  | none => return goals

structure StepsConfig where
  limit : Nat
  addLemmas : List AddLemma
  strict : Bool
  unsafeUnifySL : Bool

/--
Takes a sequence of at most `limit` steps to attempt to advance the proof state.
-/
partial def steps (mvar : MVarId) (config : StepsConfig)  : TacticM (List MVarId) := do
  let goals ← stepsLoop
    (TripleGoals.mk mvar [] [] [])
    config.addLemmas
    config.limit
    config.strict
    config.unsafeUnifySL
  return goals.flatten

theorem callDecl_direct_intro {p : Prime} {Γ : Env}
    {argTps : List Tp} {outTp : Tp}
    {fnName : Ident}
    {kinds : List Kind}
    {generics : HList Kind.denote kinds}
    {func : Function}
    {args : HList (Tp.denote p) argTps}
    {H : SLP (State p)}
    {Q : Tp.denote p outTp → SLP (State p)}
    (_h_found : (Γ.functions.find? (fun ⟨n, _⟩ => n = fnName)) = some ⟨fnName, func⟩)
    (_hkc : func.generics = kinds)
    (_htci : (func.body _ (_hkc ▸ generics) |>.argTps) = argTps)
    (_htco : (func.body _ (_hkc ▸ generics) |>.outTp) = outTp)
    (_h_hoare : STHoare p Γ H
      (_htco ▸ (func.body _ (_hkc ▸ generics) |>.body (_htci ▸ args)))
      (_htco ▸ Q))
  : STHoare p Γ H (Expr.call argTps outTp (.decl fnName kinds generics) args) Q := by
  sorry

theorem bindVar {α : Sort _} {v : α} {P : α → Prop} (hp : ∀ v, P v) : P v := hp v

theorem step_as {p : Prime} {Γ : Env} {tp : Tp}
    (H : SLP (State p)) (Q : Tp.denote p tp → SLP (State p))
    {e : Expr (Tp.denote p) tp}
  : STHoare p Γ H e Q → STHoare p Γ H e Q := id

declare_syntax_cat steps_items

syntax "[" term,* "]" : steps_items
syntax "steps" (num)? (steps_items)? optConfig : tactic

def parseStepsConfig
    (goal : MVarId)
    (unsafeUnifySL : Bool)
    (limit : Option (TSyntax `num))
    (stepsItems : Option (TSyntax `steps_items))
    (config : TSyntax `Lean.Parser.Tactic.optConfig)
  : TacticM StepsConfig := goal.withContext do
  let limit := limit.map (fun n => n.getNat) |>.getD 1000

  let addLemmas ← match stepsItems with
    | some x =>
      match x with
      | `(steps_items| [ $ts,*]) =>
        ts.getElems.toList.mapM fun term => do
          let expr ← elabTerm term none
          return AddLemma.mk expr ⟨term⟩ true
      | _ => throwError "unexpected syntax for additional lemmas"
    | none => pure []

  let optConfig := getConfigItems config
  let configItems ← optConfig.mapM fun config =>
    match config with
    | `(configItem| +$ident) => return (ident.getId, true)
    | `(configItem| -$ident) => return (ident.getId, false)
    | _ => throwError "unexpected config item {config}"

  let strict := configItems.contains (`strict, true)

  return { limit, addLemmas, strict, unsafeUnifySL }

/--
Takes a sequence of steps to attempt to advance the proof state.
-/
elab "steps" u:"unsafe"? limit:optional(num) lemmas:optional(steps_items) config:optConfig : tactic => do
  let goals ← getMainGoal
  let config ← parseStepsConfig goals u.isSome limit lemmas config
  let goals ← steps goals config
  replaceMainGoal goals

/--
Performs the next step of a program proof, manually providing the pre- and post-conditions.
-/
elab "step_as" n:optional(ident) ("=>")? "(" pre:term ")" "(" post:term ")" : tactic => do
  let goal ← getMainGoal
  trace[KanLampe.STHoare.Helpers] "step_as {n}"
  let enterer ← match n with
  | some n => ``(bindVar (fun $n => step_as $pre $post))
  | none => ``(step_as $pre $post)
  let stepAsConfig := {
    limit := 1,
    addLemmas := [AddLemma.mk (← withMainContext <| elabTerm enterer none) enterer (generalizeEnv := false)],
    strict := true,
    unsafeUnifySL := false
  }
  let newGoals ← try steps goal stepAsConfig catch e =>
    throwError "step_as failed:
    This may be because the goal is not a `letIn` the pre and post conditions are not well-formed.

    Exception returned:
    {e.toMessageData}"
  replaceMainGoal newGoals

/--
States the invariants that hold for a loop.
-/
elab "loop_inv" p:optional("nat") inv:term : tactic => do
  let solver ← if p.isSome then ``(loop_inv_intro' $inv) else ``(loop_inv_intro $inv)
  let loopInvConfig := {
    limit := 1,
    addLemmas := [AddLemma.mk (← withMainContext <| elabTerm solver none) solver (generalizeEnv := false)],
    strict := true,
    unsafeUnifySL := false
  }
  let goals ← steps (← getMainGoal) loopInvConfig
  replaceMainGoal goals


syntax (name := enterDecl) "enter_decl" : tactic

/--
Enters the declaration of a function and unfolds its body.
-/
@[tactic enterDecl]
def elabEnterDecl : Tactic := fun _ => do
  let goal ← getMainGoal
  let newGoals ← goal.applyConst ``callDecl_direct_intro

  let (some nameGoal, some continuationGoal, some genericsGoal, some argTypeGoal, some outTypeGoal) :=
    (newGoals[0]?, newGoals[1]?, newGoals[3]?, newGoals[4]?, newGoals[5]?) |
      throwError "enter_decl generated unexpected goals, expected 6 goals, got {newGoals.length}"

  pushGoal continuationGoal

  try nameGoal.refl catch _ => throwError "Unable to find a declaration in the environment with the right name"
  try genericsGoal.refl catch _ => throwError "Found declaration has the wrong generics"
  try argTypeGoal.refl catch _ => throwError "Found declaration has the wrong arguments"
  try outTypeGoal.refl catch _ => throwError "Found declaration has the wrong output type"

  evalTactic (←`(tactic|simp only))

/--
Enters the body of a locally-defined lambda.
-/
elab "enter_lambda_as" n:optional(ident) ("=>")? "(" pre:term ")" "(" post:term ")" : tactic => do
  let goal ← getMainGoal
  trace[KanLampe.STHoare.Helpers] "enter_lambda_as {n}"
  let enterer ← match n with
  | some n => ``(bindVar (fun $n => STHoare.callLambda_intro (P := $pre) (Q := $post)))
  | none => ``(STHoare.callLambda_intro (P := $pre) (Q := $post))
  let enterLambdaConfig := {
    limit := 1,
    addLemmas := [AddLemma.mk (← withMainContext <| elabTerm enterer none) enterer (generalizeEnv := false)],
    strict := true
    unsafeUnifySL := false
  }
  let newGoals ← try steps goal enterLambdaConfig catch e =>
    throwError
    m!"steps has encountered an error in proceeding.
    The returned exception is {e.toMessageData}"
  replaceMainGoal newGoals

/--
Convenience wrapper combining `steps`, `subst_vars`, and `rename_i`.
-/
elab "steps_named" ls:(steps_items)? " as " "[" ns:Lean.binderIdent,* "]" : tactic => do
  match ls with
  | some l => evalTactic (← `(tactic| steps $l:steps_items))
  | none => evalTactic (← `(tactic| steps))
  evalTactic (← `(tactic| subst_vars))
  let nsArr := ns.getElems
  evalTactic (← `(tactic| rename_i $nsArr*))

elab "steps_named" ls:(steps_items)? : tactic => do
  match ls with
  | some l => evalTactic (← `(tactic| steps $l:steps_items))
  | none => evalTactic (← `(tactic| steps))
  evalTactic (← `(tactic| subst_vars))

end KanLampe.Steps
