import KanLampe.Hoare.SepTotal

import KanLampe.Builtin.Arith
import KanLampe.Builtin.Array
import KanLampe.Builtin.Bit
import KanLampe.Builtin.Cast
import KanLampe.Builtin.Cmp
import KanLampe.Builtin.Field
import KanLampe.Builtin.Lens
import KanLampe.Builtin.Memory
import KanLampe.Builtin.Runtime
import KanLampe.Builtin.Vector
import KanLampe.Builtin.Str
import KanLampe.Builtin.Struct

/-!
# KanLampe.Hoare.Builtins

Port of `Lampe.Hoare.Builtins`.  Provides the foundational
`pureBuiltin_intro`, `pureBuiltin_intro_consequence`,
`genericTotalPureBuiltin_intro`, and `genericBuiltin_intro` lemmas,
together with total Hoare triples for every concrete builtin.

The foundational lemmas and a few triples involving direct reasoning
about the reference / lambdas heap are currently left as `sorry`
pending a dedicated builtin-semantics lemma layer.  The routine
arithmetic / comparison / bit / field / vector / string / struct /
tuple triples are derivable once the foundation is sealed, and are
listed here as `sorry`-ed declarations so that downstream tactic /
syntax layers can reference them uniformly.
-/

namespace KanLampe.STHoare

/--
Introduction rule for pure builtins.  A pure builtin call succeeds
whenever its description's precondition holds and yields the
description's output.
-/
theorem pureBuiltin_intro {p : Prime} {Γ : Env} {A : Type} {a : A}
    {sgn : A → List Tp × Tp}
    {desc : {p : Prime}
          → (a : A)
          → (args : HList (Tp.denote p) (sgn a).fst)
          → (h : Prop) × (h → (Tp.denote p (sgn a).snd))}
    {args : HList (Tp.denote p) (sgn a).fst} :
    STHoare p Γ
      ⟦⟧
      (.callBuiltin (sgn a).fst (sgn a).snd
        (Builtin.newGenericPureBuiltin sgn desc) args)
      (fun v => ∃∃ h, SLP.lift (α := State p) (v = (desc a args).snd h)) := by
  sorry

/--
A more convenient form of `pureBuiltin_intro`: given arbitrary index
equalities `h1` and `h2` and a post `Q` that holds whenever the
precondition does, one obtains a total Hoare triple for the builtin.
-/
lemma pureBuiltin_intro_consequence
    {p : Prime} {Γ : Env}
    {A : Type} {a : A} {sgn : A → List Tp × Tp}
    {desc : {p : Prime}
          → (a : A)
          → (args : HList (Tp.denote p) (sgn a).fst)
          → (h : Prop) × (h → (Tp.denote p (sgn a).snd))}
    {argTps : List Tp} {outTp : Tp}
    {args : HList (Tp.denote p) argTps}
    {Q : Tp.denote p outTp → Prop}
    (h1 : argTps = (sgn a).fst)
    (h2 : outTp = (sgn a).snd)
    (_hp : (h : (desc a (h1 ▸ args)).fst) →
        Q (h2 ▸ (desc a (h1 ▸ args)).snd h)) :
    STHoare p Γ ⟦⟧
      (.callBuiltin argTps outTp
        (Builtin.newGenericPureBuiltin sgn desc) args)
      (fun v => SLP.lift (α := State p) (Q v)) := by
  sorry

/--
Total pure builtin introduction: if a builtin is a total pure builtin
(`newGenericTotalPureBuiltin`) then we get an unconditional total
Hoare triple yielding `desc a args`.
-/
def genericTotalPureBuiltin_intro {A : Type}
    {sgn : A → List Tp × Tp}
    {desc : {p : Prime}
          → (a : A)
          → (args : HList (Tp.denote p) (sgn a).fst)
          → (Tp.denote p (sgn a).snd)}
    (b : Builtin)
    (_ : b = Builtin.newGenericTotalPureBuiltin sgn desc) :
    ∀ (a : A) (p : Prime) (Γ : Env)
      (args : HList (Tp.denote p) (sgn a).fst),
      STHoare p Γ ⟦⟧
        (.callBuiltin (sgn a).fst (sgn a).snd b args)
        (fun v => SLP.lift (α := State p) (v = desc a args)) := by
  sorry

/--
Introduction rule for generic (possibly-nondeterministic) builtins.
-/
theorem genericBuiltin_intro {p : Prime} {Γ : Env} {A : Type} {a : A}
    {sgn : A → List Tp × Tp}
    {desc : {p : Prime}
          → (a : A)
          → (args : HList (Tp.denote p) (sgn a).fst)
          → (Tp.denote p (sgn a).snd) → Prop}
    {args : HList (Tp.denote p) (sgn a).fst} :
    STHoare p Γ
      ⟦⟧
      (.callBuiltin (sgn a).fst (sgn a).snd
        (Builtin.newGenericBuiltin sgn desc) args)
      (fun v => SLP.lift (α := State p) (desc a args v)) := by
  sorry

/-! ## Arithmetic -/

theorem uAdd_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.uAdd (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem uSub_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.uSub (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem uMul_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.uMul (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem uDiv_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.uDiv (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem uRem_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.uRem (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem iAdd_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.iAdd (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem iSub_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.iSub (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem iMul_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.iMul (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem iDiv_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.iDiv (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem iRem_intro {p Γ s a b} :
    STHoarePureBuiltin p Γ Builtin.iRem (by kan_trivial) (a := s) h![a, b] := by
  sorry

theorem iNeg_intro {p Γ s a} :
    STHoarePureBuiltin p Γ Builtin.iNeg (by kan_trivial) (a := s) h![a] := by
  sorry

theorem fAdd_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.field, .field] .field Builtin.fAdd h![a, b])
      (fun v => SLP.lift (α := State p) (v = a + b)) := by
  sorry

theorem fSub_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.field, .field] .field Builtin.fSub h![a, b])
      (fun v => SLP.lift (α := State p) (v = a - b)) := by
  sorry

theorem fMul_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.field, .field] .field Builtin.fMul h![a, b])
      (fun v => SLP.lift (α := State p) (v = a * b)) := by
  sorry

theorem fDiv_intro {p Γ a b} :
    STHoarePureBuiltin p Γ Builtin.fDiv (by kan_trivial) (a := ()) h![a, b] := by
  sorry

theorem fNeg_intro {p Γ a} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.field] .field Builtin.fNeg h![a])
      (fun v => SLP.lift (α := State p) (v = -a)) := by
  sorry

/-! ## Bitwise -/

theorem bNot_intro {p Γ a} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.bool] .bool Builtin.bNot h![a])
      (fun v => SLP.lift (α := State p) (v = !a)) := by
  sorry

theorem bAnd_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.bool, .bool] .bool Builtin.bAnd h![a, b])
      (fun v => SLP.lift (α := State p) (v = (a && b))) := by
  sorry

theorem bOr_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.bool, .bool] .bool Builtin.bOr h![a, b])
      (fun v => SLP.lift (α := State p) (v = (a || b))) := by
  sorry

theorem bXor_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.bool, .bool] .bool Builtin.bXor h![a, b])
      (fun v => SLP.lift (α := State p) (v = (a ^^ b))) := by
  sorry

/-! ## Comparison -/

theorem unitEq_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.unit, .unit] .bool Builtin.unitEq h![a, b])
      (fun v => SLP.lift (α := State p) (v = (a == b))) := by
  sorry

theorem bEq_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.bool, .bool] .bool Builtin.bEq h![a, b])
      (fun v => SLP.lift (α := State p) (v = (a == b))) := by
  sorry

theorem fEq_intro {p Γ a b} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [.field, .field] .bool Builtin.fEq h![a, b])
      (fun v => SLP.lift (α := State p) (v = (a == b))) := by
  sorry

/-! ## Arrays / Vectors -/

theorem arrayIndex_intro {p Γ tp n arr i} :
    STHoarePureBuiltin p Γ Builtin.arrayIndex (by kan_trivial)
      (a := (tp, n)) h![arr, i] := by
  sorry

theorem asVector_intro {p Γ tp n arr} :
    STHoarePureBuiltin p Γ Builtin.asVector (by kan_trivial)
      (a := (tp, n)) h![arr] := by
  sorry

theorem vectorIndex_intro {p Γ tp sl i} :
    STHoarePureBuiltin p Γ Builtin.vectorIndex (by kan_trivial)
      (a := tp) h![sl, i] := by
  sorry

/-! ## Memory (reference builtins) -/

theorem ref_intro {p Γ tp} {v : Tp.denote p tp} :
    STHoare p Γ
      ⟦⟧
      (.callBuiltin [tp] (.ref tp) Builtin.ref h![v])
      (fun r => [r ↦ ⟨tp, v⟩]) := by
  sorry

theorem readRef_intro {p Γ tp r} {v : Tp.denote p tp} :
    STHoare p Γ
      [r ↦ ⟨tp, v⟩]
      (.callBuiltin [.ref tp] tp Builtin.readRef h![r])
      (fun v' => ⟦v' = v⟧ ⋆ [r ↦ ⟨tp, v⟩]) := by
  sorry

theorem writeRef_intro {p Γ tp r} {v v' : Tp.denote p tp} :
    STHoare p Γ
      [r ↦ ⟨tp, v⟩]
      (.callBuiltin [.ref tp, tp] .unit Builtin.writeRef h![r, v'])
      (fun _ => [r ↦ ⟨tp, v'⟩]) := by
  sorry

/-! ## Cast -/

theorem cast_intro {p Γ tp tp'} [Builtin.CastTp tp tp']
    {v : Tp.denote p tp} :
    STHoare p Γ ⟦⟧
      (.callBuiltin [tp] tp' Builtin.cast h![v])
      (fun v' =>
        SLP.lift (α := State p)
          (v' = @Builtin.CastTp.cast tp tp' _ p v)) := by
  sorry

/-!
## Placeholder stubs for intro lemmas referenced by `KanLampe.Tactic.Steps`

These declarations are recognized by name in `getClosingTerm` so that
the `steps` tactic elaborates.  Their bodies are inhabited only so the
identifiers resolve; any use of them at tactic runtime will obviously
fail.  They should be replaced with proper statements as the
corresponding upstream lemmas are ported.
-/

theorem uLeq_intro : True := trivial
theorem iShl_intro : True := trivial
theorem iShr_intro : True := trivial
theorem assert_intro : True := trivial
theorem staticAssert_intro : True := trivial
theorem strAsBytes_intro : True := trivial
theorem arrayAsStrUnchecked_intro : True := trivial
theorem vector_arrayLen_intro : True := trivial
theorem array_arrayLen_intro : True := trivial
theorem applyRangeConstraint_intro : True := trivial
theorem fModNumBits_intro : True := trivial
theorem toLeBits_intro : True := trivial
theorem toBeBits_intro : True := trivial
theorem toLeRadix_intro : True := trivial
theorem toBeRadix_intro : True := trivial
theorem getLens_intro : True := trivial
theorem modifyLens_intro : True := trivial
theorem loop_inv_intro : True := trivial
theorem loop_inv_intro' : True := trivial

end KanLampe.STHoare
