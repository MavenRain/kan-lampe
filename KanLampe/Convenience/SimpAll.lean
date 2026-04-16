import KanTactics
import Lean.Meta.Tactic.Simp.SimpAll
import Lean.Meta.Tactic.Simp.Attr

/-!
# KanLampe.Convenience.SimpAll

Native implementation of `simp_all` using a dedicated `@[kan_simp]`
simp set.  No call to Lean's built-in `simp_all` tactic.

## Categorical story

Same as the Normalize family: transport in the sub-groupoid of the
simp lemma set, applied simultaneously to the goal and every
hypothesis in context.  `simp_all` iterates the Normalize Kan
extension over all Prop-typed hypotheses until a fixpoint is reached.

## The `@[kan_simp]` attribute

Lemmas tagged with `@[kan_simp]` populate a dedicated simp set that
augments the default `@[simp]` set when `kan_simp_all` runs.  This
gives kan-lampe a private slot for adding project-specific rewrites
without polluting Mathlib's global simp database, while still
inheriting Lean's standard rewrite library.

The combined lemma set used by `kan_simp_all` is therefore:

    default @[simp]  ∪  @[kan_simp]  ∪  inline lemmas

To tag a lemma:

    @[kan_simp] theorem my_lemma : ... := ...

To use the attribute transitively with extra inline lemmas:

    by kan_simp_all [extraLemma1, extraLemma2]

## Reduction to the spanning set

`kan_simp_all` invokes `Lean.Meta.simpAll` directly (the same
primitive used by Lean's built-in `simp_all`, at the Meta level
rather than via `evalTactic`).  This is consistent with the
`kan_simp` primitive in `KanTactics.Tactic.Normalize`, which calls
`Simp.main` directly.  The Kan extension interpretation is the same
as for `kan_simp`: a Normalize extension over the custom lemma set.

No new `KanExtensionKind` is introduced.
-/

open Lean Meta Elab Tactic

set_option autoImplicit false

namespace KanLampe.SimpAll

/-- The `kan_simp` attribute registers a lemma into the dedicated
    kan-lampe simp set.  Use via `@[kan_simp] theorem ...`. -/
initialize kanSimpExt : SimpExtension ←
  registerSimpAttr `kan_simp "kan-lampe dedicated simp set"

/-- Add a single external name to a `SimpTheorems` set, dispatching
    between theorem-as-rewrite (`addConst`) and definition-as-unfolder
    (`addDeclToUnfold`) based on the declaration's kind. -/
def addExtra (st : SimpTheorems) (n : Name) : MetaM SimpTheorems := do
  let env ← getEnv
  (env.find? n).elim (pure st) fun info =>
    match info with
    | .thmInfo _    => st.addConst n
    | .axiomInfo _  => st.addConst n
    | .defnInfo _   => st.addDeclToUnfold n
    | .opaqueInfo _ => st.addDeclToUnfold n
    | .quotInfo _   => pure st
    | .inductInfo _ => pure st
    | .ctorInfo _   => pure st
    | .recInfo _    => pure st

/-- Build a `Simp.Context` seeded with the default `@[simp]` set and
    the `@[kan_simp]` set as two separate entries in the simp-theorems
    array.  `extraNames` are added on top of the default set. -/
def mkKanSimpAllCtx (extraNames : Array Name) : MetaM Simp.Context := do
  let defaultSet ← getSimpTheorems
  let kanSet ← kanSimpExt.getTheorems
  let mut withExtras := defaultSet
  for n in extraNames do
    withExtras ← addExtra withExtras n
  let congr ← getSimpCongrTheorems
  Simp.mkContext (simpTheorems := #[withExtras, kanSet]) (congrTheorems := congr)

/-- Run `Lean.Meta.simpAll` with the kan-lampe simp context.  Returns
    the updated main goal (or closes it).  Raises an error if
    `simpAll` fails. -/
def runKanSimpAll (mvarId : MVarId) (extraNames : Array Name) : TacticM Unit := do
  mvarId.withContext do
    let ctx ← mkKanSimpAllCtx extraNames
    let ctx := ctx.setFailIfUnchanged false
    let (result, _) ← Lean.Meta.simpAll mvarId ctx
    result.elim (replaceMainGoal []) (replaceMainGoal [·])

/-- Resolve a term-syntax argument to a single declaration name,
    using `realizeGlobalConstNoOverload` so that polymorphic
    constants are handled without forcing universe/instance
    elaboration.  Returns `none` on failure. -/
def syntaxToConst (stx : Syntax) : TacticM (Option Name) :=
  (try
    let declName ← Lean.realizeGlobalConstNoOverload stx
    pure (some declName)
  catch _ => pure none)

end KanLampe.SimpAll

/-- Native `simp_all` via the spanning set, using the dedicated
    `@[kan_simp]` attribute as its lemma set.  See the module
    docstring for the categorical story. -/
elab "kan_simp_all" : tactic => do
  let mvarId ← getMainGoal
  KanLampe.SimpAll.runKanSimpAll mvarId #[]

/-- `kan_simp_all` with extra simp lemmas passed inline.  Each lemma
    must be a bare constant reference; more complex simp-lemma syntax
    (rewrites, configs, `← h`, etc.) is not supported. -/
elab "kan_simp_all " "[" lemmas:term,* "]" : tactic => do
  let mvarId ← getMainGoal
  let mut names : Array Name := #[]
  for stx in lemmas.getElems do
    names := (← KanLampe.SimpAll.syntaxToConst stx).elim names names.push
  KanLampe.SimpAll.runKanSimpAll mvarId names
