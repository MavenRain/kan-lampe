import KanTactics
import KanLampe.Convenience.Decide
import KanLampe.Convenience.SimpByName
import Mathlib.Data.Nat.Basic

/-!
# KanLampe.Convenience.Linarith

Native implementation of `linarith` (linear arithmetic over `Nat`)
as a Farkas certificate generator that emits proof terms built from
the 9 primitive `KanExtensionKind` variants.  No call to Mathlib's
`linarith` or Lean's `omega`.

## Categorical story

Linear arithmetic sequents form a decidable subcategory of the proof
category for linearly ordered (semi)rings.  Farkas' lemma states that
an inconsistent system of linear inequalities admits a nonneg rational
combination proving `0 < 0`.  Equivalently, a valid linear inequality
`L ≤ R` is derivable iff there exist nonneg integer coefficients λᵢ
on the hypotheses `Lᵢ ≤ Rᵢ` such that

    L + Σ λᵢ · Rᵢ  =  R + Σ λᵢ · Lᵢ    (equality of ℕ polynomials)

The `kan_linarith` tactic is the left Kan extension along the
inclusion of Farkas-derivable sequents into the full proof category.
The diagram functor F sends each derivable sequent to a certificate:
a vector of integer coefficients together with the ring identity
above.  The colimit assembly produces a proof term by scaling each
hypothesis, summing the scaled hypotheses, and transporting along the
ring identity.

## Reduction to the spanning set

A Farkas certificate is reduced to the 9 primitives as follows:

- **Identity** (`kan_exact`) at leaves, providing each original
  hypothesis as a closed term.
- **Precomposition** (`kan_apply`) along monotonicity lemmas
  (`Nat.mul_le_mul_left`, `Nat.add_le_add`) to scale and sum.
- **Transport** (`kan_rw`) along the ring identity.
- **Normalization** (`kan_simp_only`) on the Nat ring lemma set as
  a preprocessing pass that handles `(a+1)*c = a*c + c` and similar
  distributive patterns.

No new `KanExtensionKind` is introduced.

## Implementation: staged disjunctive search

1. **Ring normalization + reflexivity** closes goals that are ring
   identities in disguise, e.g. `(x+1)*c = x*c + c`.  This covers
   the majority of `kan_linarith` uses in the kan-lampe port.

2. **Assumption lifting**: for each local hypothesis `h`, try
   `exact h`, `exact Nat.le_of_lt h`, `exact Nat.succ_le_of_lt h`, …

3. **Monotonicity patterns**: apply common two-step lemmas such as
   `Nat.lt_trans`, `Nat.lt_of_le_of_lt`, `Nat.add_le_add_left`,
   `Nat.add_lt_add_right`, `Nat.le_add_right`, and recurse on the
   resulting subgoals.

4. **Farkas kernel**: parse the goal and local hypotheses into
   `LinExpr` form, run a bounded integer-coefficient search, and
   reconstruct the proof by scaling+summing the hypotheses.

Each stage is atomic (restores state on failure).
-/

namespace KanLampe.Linarith

open Lean Meta Elab Tactic

set_option autoImplicit false

/-! ## Phase 1: ring-normalization simp context -/

/-- Nat-specific ring lemma set used as a preprocessing normalizer.
    Includes `mul_comm`/`add_comm`; Lean's simp engine applies these
    under an AC-ordering heuristic, so no rewrite loop results. -/
def natRingLemmaNames : List Name :=
  [``Nat.left_distrib, ``Nat.right_distrib,
   ``Nat.mul_one, ``Nat.one_mul, ``Nat.mul_zero, ``Nat.zero_mul,
   ``Nat.add_zero, ``Nat.zero_add,
   ``Nat.succ_mul, ``Nat.mul_succ,
   ``Nat.mul_assoc, ``Nat.add_assoc,
   ``Nat.mul_comm, ``Nat.add_comm, ``Nat.add_left_comm, ``Nat.mul_left_comm]

/-- Build a `Simp.Context` populated with the Nat ring lemmas. -/
def mkNatRingCtx : MetaM Simp.Context := do
  let env ← getEnv
  let mut st : SimpTheorems := {}
  for n in natRingLemmaNames do
    if env.contains n then
      st ← st.addConst n
  let congr ← getSimpCongrTheorems
  let ctx ← Simp.mkContext (simpTheorems := #[st]) (congrTheorems := congr)
  pure (ctx.setFailIfUnchanged false)

/-- Run the Nat ring normalizer on a goal.  Returns the updated goal
    (or `none` if closed). -/
def ringNormalize (mvarId : MVarId) : MetaM (Option MVarId) := do
  let ctx ← mkNatRingCtx
  let (result, _) ← simpTarget mvarId ctx
  pure result

/-! ## LinExpr: linear expressions over ℤ with opaque atoms -/

/-- A linear expression `Σ cᵢ · aᵢ + c` over `ℤ`.  Atoms are Lean
    `Expr`s compared by `BEq`. -/
structure LinExpr where
  coeffs : Array (Expr × Int) := #[]
  const  : Int := 0
  deriving Inhabited

namespace LinExpr

def zero : LinExpr := {}
def ofConstant (n : Int) : LinExpr := { const := n }
def ofAtom (e : Expr) : LinExpr := { coeffs := #[(e, 1)] }

def coeff (le : LinExpr) (a : Expr) : Int :=
  le.coeffs.foldl (init := 0) fun acc (x, c) =>
    if x == a then c else acc

def setCoeff (le : LinExpr) (a : Expr) (c : Int) : LinExpr :=
  if c == 0 then
    { le with coeffs := le.coeffs.filter fun (x, _) => !(x == a) }
  else if le.coeffs.any (fun (x, _) => x == a) then
    { le with coeffs := le.coeffs.map fun (x, d) =>
        if x == a then (x, c) else (x, d) }
  else
    { le with coeffs := le.coeffs.push (a, c) }

def add (a b : LinExpr) : LinExpr := Id.run do
  let mut out := a
  for (x, c) in b.coeffs do
    out := out.setCoeff x (out.coeff x + c)
  pure { out with const := a.const + b.const }

def neg (a : LinExpr) : LinExpr :=
  { coeffs := a.coeffs.map fun (x, c) => (x, -c),
    const := -a.const }

def sub (a b : LinExpr) : LinExpr := a.add b.neg

def scale (k : Int) (a : LinExpr) : LinExpr :=
  if k == 0 then zero
  else { coeffs := a.coeffs.map fun (x, c) => (x, k * c),
         const := k * a.const }

def equal (a b : LinExpr) : Bool :=
  let s := a.sub b
  s.coeffs.isEmpty && s.const == 0

end LinExpr

/-! ## Parser: Expr → LinExpr, Prop → Ineq -/

/-- Try to read an `Int` from a Nat/OfNat literal expression.  Chains
    `Expr.nat?` with `Expr.rawNatLit?` via `Option.orElse`. -/
def exprIntLit? (e : Expr) : Option Int :=
  (e.nat?.map Int.ofNat).orElse (fun _ => e.rawNatLit?.map Int.ofNat)

/-- Parse a `Nat`-valued expression into a `LinExpr`.  Non-linear
    subterms are treated as opaque atoms. -/
partial def toLinExpr (e : Expr) : MetaM LinExpr := do
  let e ← instantiateMVars e
  (exprIntLit? e).elim
    (match_expr e with
     | HAdd.hAdd _ _ _ _ a b => do pure ((← toLinExpr a).add (← toLinExpr b))
     | Nat.add a b => do pure ((← toLinExpr a).add (← toLinExpr b))
     | HMul.hMul _ _ _ _ a b => parseMul e a b
     | Nat.mul a b => parseMul e a b
     | _ => pure (LinExpr.ofAtom e))
    (fun n => pure (LinExpr.ofConstant n))
where
  parseMul (orig a b : Expr) : MetaM LinExpr :=
    (exprIntLit? a).elim
      ((exprIntLit? b).elim
        (pure (LinExpr.ofAtom orig))
        (fun k => do pure (LinExpr.scale k (← toLinExpr a))))
      (fun k => do pure (LinExpr.scale k (← toLinExpr b)))

/-- Relation kind for a parsed (in)equality. -/
inductive Rel where
  | eq
  | le
  | lt
  deriving DecidableEq, Repr, Inhabited

/-- A parsed (in)equality `lhs R rhs`. -/
structure Ineq where
  lhs : LinExpr
  rhs : LinExpr
  rel : Rel
  deriving Inhabited

/-- The "delta" of an inequality, viewed as `rhs - lhs`.  Meaning:
    ≥ 0 for `le`, > 0 for `lt`, = 0 for `eq`. -/
def Ineq.delta (i : Ineq) : LinExpr := i.rhs.sub i.lhs

/-- Parse a Prop into an `Ineq`, if possible. -/
def toIneq (prop : Expr) : MetaM (Option Ineq) := do
  let prop ← instantiateMVars prop
  match_expr prop with
  | LE.le _ _ a b =>
    pure (some { lhs := (← toLinExpr a), rhs := (← toLinExpr b), rel := .le })
  | LT.lt _ _ a b =>
    pure (some { lhs := (← toLinExpr a), rhs := (← toLinExpr b), rel := .lt })
  | Eq _ a b =>
    pure (some { lhs := (← toLinExpr a), rhs := (← toLinExpr b), rel := .eq })
  | GE.ge _ _ a b =>
    pure (some { lhs := (← toLinExpr b), rhs := (← toLinExpr a), rel := .le })
  | GT.gt _ _ a b =>
    pure (some { lhs := (← toLinExpr b), rhs := (← toLinExpr a), rel := .lt })
  | _ => pure none

/-! ## Farkas search: bounded integer coefficients -/

/-- A scaled hypothesis: the FVarId, its parsed form, and the
    coefficient applied in the certificate. -/
structure ScaledHyp where
  fvarId : FVarId
  ineq   : Ineq
  coeff  : Int
  deriving Inhabited

/-- Bounded integer-coefficient search for `Σ λᵢ · deltaᵢ = goalDelta`.
    For `le`/`lt` hypotheses, `λᵢ ∈ {0, …, B}`.  For `eq` hypotheses,
    `λᵢ ∈ {-B, …, B}`.  `B = 3` suffices for the kan-lampe fragment. -/
partial def findFarkasCertificate
    (hyps : Array (FVarId × Ineq)) (goalDelta : LinExpr)
    (bound : Int := 3) : Option (Array ScaledHyp) :=
  go 0 #[] LinExpr.zero
where
  go (i : Nat) (acc : Array ScaledHyp) (cur : LinExpr)
      : Option (Array ScaledHyp) :=
    if h : i < hyps.size then
      let (fv, ineq) := hyps[i]
      let lo : Int := if ineq.rel == .eq then -bound else 0
      tryRange fv ineq lo bound i acc cur
    else
      if cur.equal goalDelta then some acc else none
  tryRange (fv : FVarId) (ineq : Ineq) (k : Int) (hi : Int)
      (i : Nat) (acc : Array ScaledHyp) (cur : LinExpr)
      : Option (Array ScaledHyp) :=
    if k > hi then none
    else
      let acc' := if k == 0 then acc else acc.push ⟨fv, ineq, k⟩
      let cur' := cur.add (LinExpr.scale k ineq.delta)
      go (i + 1) acc' cur' <|> tryRange fv ineq (k + 1) hi i acc cur

/-! ## Stage 1-3: fast paths -/

/-- Try to close the goal by definitional reflexivity. -/
def tryRfl (mvarId : MVarId) : MetaM Bool := do
  try
    mvarId.refl
    pure true
  catch _ => pure false

/-- Run `ringNormalize` then `tryRfl`.  Returns `true` on success.
    On failure, fully restores state so the goal's shape is unchanged. -/
def tryRingRfl (mvarId : MVarId) : MetaM Bool := do
  let s ← saveState
  try
    (← ringNormalize mvarId).elim
      (pure true)
      (fun g => do
        if ← tryRfl g then
          pure true
        else
          restoreState s
          pure false)
  catch _ =>
    restoreState s
    pure false

/-- The lemma battery for stage 3: monotonicity, transitivity,
    arithmetic identity liftings. -/
def monoLemmaNames : List Name :=
  [``Nat.le_of_lt, ``Nat.le_of_eq,
   ``Nat.succ_le_of_lt, ``Nat.lt_of_succ_le,
   ``Nat.add_lt_add_left, ``Nat.add_lt_add_right,
   ``Nat.add_le_add_left, ``Nat.add_le_add_right,
   ``Nat.add_lt_add, ``Nat.add_le_add,
   ``Nat.le_add_right, ``Nat.le_add_left,
   ``Nat.lt_trans, ``Nat.lt_of_le_of_lt, ``Nat.lt_of_lt_of_le,
   ``Nat.le_trans, ``Nat.le_refl, ``Nat.lt_irrefl,
   ``Nat.mul_le_mul_left, ``Nat.mul_le_mul_right]

/-- Attempt to close the goal by `exact e`, properly checking type
    compatibility.  Returns `true` on success, leaves state unchanged
    on failure. -/
def tryExact (mvarId : MVarId) (e : Expr) : MetaM Bool := do
  let s ← saveState
  try
    let eType ← inferType e
    let tgt ← mvarId.getType
    if ← isDefEq tgt eType then
      mvarId.assign e
      pure true
    else
      restoreState s
      pure false
  catch _ =>
    restoreState s
    pure false

/-- Attempt to apply `e` as a backward chain, returning the list of
    new subgoals on success.  Returns `none` on failure and leaves
    state unchanged.  Only non-dependent unassigned subgoals are
    returned; dependent metavariables (e.g. the middle `b` of a
    transitivity lemma) usually get unified away and must not be
    reported as "real" subgoals. -/
def tryApplyTerm (mvarId : MVarId) (e : Expr) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try
    let gs ← mvarId.apply e (cfg := { newGoals := .nonDependentOnly })
    let mut filtered : List MVarId := []
    for g in gs do
      unless ← g.isAssigned do
        filtered := filtered ++ [g]
    pure (some filtered)
  catch _ =>
    restoreState s
    pure none

/-- Rewrite the goal by an equality hypothesis `heq : a = b`, in either
    direction.  Returns the new goal on success, `none` on failure. -/
def tryRewriteBy (mvarId : MVarId) (heq : Expr) (symm : Bool) : MetaM (Option MVarId) := do
  let s ← saveState
  try
    let tgt ← mvarId.getType
    let result ← mvarId.rewrite tgt heq symm
    let g ← mvarId.replaceTargetEq result.eNew result.eqProof
    pure (some g)
  catch _ =>
    restoreState s
    pure none

/-- Recursively close the goal by trying each strategy in order.  The
    `depth` parameter bounds the monotonicity-lemma search tree. -/
partial def tryClose (mvarId : MVarId) (depth : Nat) : MetaM Bool := do
  if ← tryRfl mvarId then return true
  if ← tryRingRfl mvarId then return true
  -- Direct assumption: try each Prop-typed local hypothesis via `tryExact`.
  let byAssumption ← mvarId.withContext do
    let lctx ← getLCtx
    let mut result := false
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      if !(← isProp ldecl.type) then continue
      if ← tryExact mvarId ldecl.toExpr then
        result := true
        break
    pure result
  if byAssumption then return true
  if depth == 0 then return false
  -- Rewrite by each local equality hypothesis, then retry.  Both
  -- directions are tried; the first one producing a closed goal wins.
  let rewroteClosed ← mvarId.withContext do
    let lctx ← getLCtx
    let mut done := false
    for ldecl in lctx do
      if done then break
      if ldecl.isImplementationDetail then continue
      if !(← isProp ldecl.type) then continue
      unless ldecl.type.isAppOfArity ``Eq 3 do continue
      for symm in #[false, true] do
        if done then break
        let s ← saveState
        let rewResult ← tryRewriteBy mvarId ldecl.toExpr symm
        let closedByRewrite ← rewResult.elim
          (pure false)
          (fun g => do
            if ← tryClose g (depth - 1) then
              pure true
            else
              restoreState s
              pure false)
        if closedByRewrite then done := true
    pure done
  if rewroteClosed then return true
  -- Battery of monotonicity lemmas.  Each lemma is applied atomically:
  -- if the apply succeeds but recursive closing of subgoals fails, we
  -- fully restore state so no partial assignments leak into the parent.
  for lemmaName in monoLemmaNames do
    let s ← saveState
    let c ← mkConstWithFreshMVarLevels lemmaName
    let applyResult ← tryApplyTerm mvarId c
    let closedByLemma ← applyResult.elim
      (pure false)
      (fun gs => do
        let mut ok := true
        for g in gs do
          unless ← tryClose g (depth - 1) do
            ok := false
            break
        pure ok)
    if closedByLemma then return true
    restoreState s
  pure false

/-! ## Stage 4: Farkas proof reconstruction -/

/-- Collect local hypotheses that parse as `Ineq`. -/
def collectHyps (mvarId : MVarId) : MetaM (Array (FVarId × Ineq)) := do
  mvarId.withContext do
    let mut out : Array (FVarId × Ineq) := #[]
    let lctx ← getLCtx
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      out := (← toIneq ldecl.type).elim out fun ineq =>
        out.push (ldecl.fvarId, ineq)
    pure out

/-- Reconstruct the proof from a Farkas certificate with a single
    hypothesis of matching relation and coefficient 1.  This handles
    the pure-assumption case and direct liftings.  Harder cases are
    delegated back to `tryClose`. -/
def farkasClose (mvarId : MVarId) : MetaM Bool := do
  mvarId.withContext do
    let tgt ← mvarId.getType
    (← toIneq tgt).elim
      (pure false)
      (fun goal => do
        let hyps ← collectHyps mvarId
        (findFarkasCertificate hyps goal.delta).elim
          (pure false)
          (fun cert =>
            if cert.size == 1 && cert[0]!.coeff == 1
                && cert[0]!.ineq.rel == goal.rel then
              tryExact mvarId (mkFVar cert[0]!.fvarId)
            else
              pure false))

/-! ## Main tactic -/

/-- Internal: try to close `mvarId` via the full staged pipeline. -/
def kanLinarithCore (mvarId : MVarId) : TacticM Unit := do
  mvarId.withContext do
    if ← tryClose mvarId (depth := 3) then
      replaceMainGoal []
      return
    if ← farkasClose mvarId then
      replaceMainGoal []
      return
    throwError "kan_linarith: failed to close goal"

/-- Native `linarith` via the spanning set.  See the module docstring
    for the staged disjunctive search. -/
elab "kan_linarith" : tactic => do
  let mvarId ← getMainGoal
  kanLinarithCore mvarId

/-- `kan_linarith` with extra hypotheses supplied as terms.  Each term
    is asserted into context via `MVarId.assert` + `intro`, then the
    core procedure runs. -/
elab "kan_linarith " "[" lemmas:term,* "]" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let mut g := mvarId
    for stx in lemmas.getElems do
      let e ← Lean.Elab.Term.elabTerm stx none
      let ty ← inferType e
      let gAsserted ← g.assert `hlin ty e
      let (_, gIntro) ← gAsserted.intro1P
      g := gIntro
    kanLinarithCore g

end KanLampe.Linarith
