import KanLampe.Ast
import KanLampe.Data.Field
import KanLampe.Semantics.Env
import KanLampe.Semantics.Trait
import KanLampe.SeparationLogic.State

/-!
# KanLampe.Semantics

Port of `Lampe.Semantics`.  Defines the `Omni` big-step predicate
together with its `consequence`, `frame`, and `is_mono` laws.
-/

namespace KanLampe

/-- Omnisemantics for Noir programs.  See upstream `Lampe.Semantics`
for the full discussion. -/
inductive Omni (p : Prime) :
    (Γ : Env) → (st : State p) → {tp : Tp} → (expr : Expr (Tp.denote p) tp) →
    (Q : Option (State p × Tp.denote p tp) → Prop) → Prop where
| litField {Γ : Env} {st : State p} {n : Int}
    {Q : Option (State p × Tp.denote p .field) → Prop} :
    Q (some (st, (n : Fp p))) →
    Omni p Γ st (.litNum .field n) Q
| litStr {Γ : Env} {st : State p} {u : U 32} {ns : NoirStr u.toNat}
    {Q : Option (State p × Tp.denote p (.str u)) → Prop} :
    Q (some (st, ns)) →
    Omni p Γ st (.litStr u ns) Q
| fmtStr {Γ : Env} {st : State p} {u : U 32} {tps : Tp}
    {ns : FormatString u tps}
    {Q : Option (State p × Tp.denote p (.fmtStr u tps)) → Prop} :
    Q (some (st, ns)) →
    Omni p Γ st (.fmtStr u tps ns) Q
| litFalse {Γ : Env} {st : State p}
    {Q : Option (State p × Tp.denote p .bool) → Prop} :
    Q (some (st, false)) →
    Omni p Γ st (.litNum .bool 0) Q
| litTrue {Γ : Env} {st : State p}
    {Q : Option (State p × Tp.denote p .bool) → Prop} :
    Q (some (st, true)) →
    Omni p Γ st (.litNum .bool 1) Q
| litU {Γ : Env} {st : State p} {s : Nat} {n : Int}
    {Q : Option (State p × Tp.denote p (.u s)) → Prop} :
    Q (some (st, (n : U s))) →
    Omni p Γ st (.litNum (.u s) n) Q
| litI {Γ : Env} {st : State p} {s : Nat} {n : Int}
    {Q : Option (State p × Tp.denote p (.i s)) → Prop} :
    Q (some (st, (n : I s))) →
    Omni p Γ st (.litNum (.i s) n) Q
| litUnit {Γ : Env} {st : State p} {n : Int}
    {Q : Option (State p × Tp.denote p .unit) → Prop} :
    Q (some (st, ())) →
    Omni p Γ st (.litNum .unit n) Q
| constFp {Γ : Env} {st : State p} {c : Int}
    {Q : Option (State p × Tp.denote p .field) → Prop} :
    Q (some (st, (c : Fp p))) →
    Omni p Γ st (.constFp c) Q
| constU {Γ : Env} {st : State p} {w : Nat} {c : U w}
    {Q : Option (State p × Tp.denote p (.u w)) → Prop} :
    Q (some (st, c)) →
    Omni p Γ st (.constU c) Q
| fn {Γ : Env} {st : State p} {argTps : List Tp} {outTp : Tp}
    {r : FuncRef argTps outTp}
    {Q : Option (State p × Tp.denote p (.fn argTps outTp)) → Prop} :
    Q (some (st, r)) →
    Omni p Γ st (.fn argTps outTp r) Q
| var {Γ : Env} {st : State p} {tp : Tp} {v : Tp.denote p tp}
    {Q : Option (State p × Tp.denote p tp) → Prop} :
    Q (some (st, v)) →
    Omni p Γ st (.var v) Q
| skip {Γ : Env} {st : State p}
    {Q : Option (State p × Tp.denote p .unit) → Prop} :
    Q (some (st, ())) →
    Omni p Γ st .skip Q
| iteTrue {Γ : Env} {st : State p} {a : Tp}
    {mainBranch elseBranch : Expr (Tp.denote p) a}
    {Q : Option (State p × Tp.denote p a) → Prop} :
    Omni p Γ st mainBranch Q →
    Omni p Γ st (Expr.ite true mainBranch elseBranch) Q
| iteFalse {Γ : Env} {st : State p} {a : Tp}
    {mainBranch elseBranch : Expr (Tp.denote p) a}
    {Q : Option (State p × Tp.denote p a) → Prop} :
    Omni p Γ st elseBranch Q →
    Omni p Γ st (Expr.ite false mainBranch elseBranch) Q
| letIn {Γ : Env} {st : State p} {t₁ t₂ : Tp}
    {e : Expr (Tp.denote p) t₁} {b : Tp.denote p t₁ → Expr (Tp.denote p) t₂}
    {Q₁ : Option (State p × Tp.denote p t₁) → Prop}
    {Q : Option (State p × Tp.denote p t₂) → Prop} :
    Omni p Γ st e Q₁ →
    (∀ v st', Q₁ (some (st', v)) → Omni p Γ st' (b v) Q) →
    (Q₁ none → Q none) →
    Omni p Γ st (.letIn e b) Q
| callTrait {Γ : Env} {vh : ValHeap p} {lambdas : Lambdas p}
    {argTps : List Tp} {outTp : Tp} {fnRef : FuncRef argTps outTp}
    {selfTp : Tp} {traitName : String} {traitKinds : List Kind}
    {traitGenerics : HList Kind.denote traitKinds}
    {fnName : String} {kinds : List Kind}
    {generics : HList Kind.denote kinds}
    {impls : List (Ident × Function)} {fn : Function}
    {args : HList (Tp.denote p) argTps}
    {Q : Option (State p × Tp.denote p outTp) → Prop} :
    fnRef = (.trait selfTp traitName traitKinds traitGenerics fnName kinds generics) →
    TraitResolution Γ ⟨⟨traitName, traitKinds, traitGenerics⟩, selfTp⟩ impls →
    (fnName, fn) ∈ impls →
    (hkc : fn.generics = kinds) →
    (htci : (fn.body (Tp.denote p) (hkc ▸ generics) |>.argTps) = argTps) →
    (htco : (fn.body (Tp.denote p) (hkc ▸ generics) |>.outTp) = outTp) →
    Omni p Γ ⟨vh, lambdas⟩
        (htco ▸ (fn.body (Tp.denote p) (hkc ▸ generics) |>.body (htci ▸ args))) Q →
    Omni p Γ ⟨vh, lambdas⟩ (Expr.call argTps outTp fnRef args) Q
| callLambda {Γ : Env} {vh : ValHeap p} {lambdas : Lambdas p}
    {argTps : List Tp} {outTp : Tp} {fnRef : FuncRef argTps outTp} {ref : Ref}
    {lambdaBody : HList (Tp.denote p) argTps → Expr (Tp.denote p) outTp}
    {args : HList (Tp.denote p) argTps}
    {Q : Option (State p × Tp.denote p outTp) → Prop} :
    fnRef = (.lambda ref) →
    lambdas.lookup ref = some ⟨argTps, outTp, lambdaBody⟩ →
    Omni p Γ ⟨vh, lambdas⟩ (lambdaBody args) Q →
    Omni p Γ ⟨vh, lambdas⟩ (Expr.call argTps outTp fnRef args) Q
| callDecl {Γ : Env} {vh : ValHeap p} {lambdas : Lambdas p}
    {argTps : List Tp} {outTp : Tp} {fnRef : FuncRef argTps outTp}
    {fnName : String} {kinds : List Kind}
    {generics : HList Kind.denote kinds} {fn : Function}
    {args : HList (Tp.denote p) argTps}
    {Q : Option (State p × Tp.denote p outTp) → Prop} :
    fnRef = (.decl fnName kinds generics) →
    ⟨fnName, fn⟩ ∈ Γ.functions →
    (hkc : fn.generics = kinds) →
    (htci : (fn.body (Tp.denote p) (hkc ▸ generics) |>.argTps) = argTps) →
    (htco : (fn.body (Tp.denote p) (hkc ▸ generics) |>.outTp) = outTp) →
    Omni p Γ ⟨vh, lambdas⟩
        (htco ▸ (fn.body (Tp.denote p) (hkc ▸ generics) |>.body (htci ▸ args))) Q →
    Omni p Γ ⟨vh, lambdas⟩ (Expr.call argTps outTp fnRef args) Q
| lam {Γ : Env} {vh : ValHeap p} {lambdas : Lambdas p}
    {argTps : List Tp} {outTp : Tp}
    {lambdaBody : HList (Tp.denote p) argTps → Expr (Tp.denote p) outTp}
    {Q : Option (State p × Tp.denote p (.fn argTps outTp)) → Prop} :
    (∀ ref, ref ∉ lambdas →
        Q (some (⟨vh, lambdas.insert ref ⟨argTps, outTp, lambdaBody⟩⟩,
                  FuncRef.lambda ref))) →
    Omni p Γ ⟨vh, lambdas⟩ (Expr.lam argTps outTp lambdaBody) Q
| callBuiltin {Γ : Env} {st : State p} {argTps : List Tp} {outTp : Tp}
    {b : Builtin} {args : HList (Tp.denote p) argTps}
    {Q : Option (State p × Tp.denote p outTp) → Prop} :
    (b.omni p st.vals argTps outTp args (mapToValHeapCondition st.lambdas Q)) →
    Omni p Γ st (Expr.callBuiltin argTps outTp b args) Q
| loopDone {Γ : Env} {st : State p} {s : Nat} {r : Tp}
    {lo hi : U s} {body : Tp.denote p (.u s) → Expr (Tp.denote p) r}
    {Q : Option (State p × Tp.denote p .unit) → Prop} :
    lo ≥ hi →
    Q (some (st, ())) →
    Omni p Γ st (.loop lo hi body) Q
| loopNext {Γ : Env} {st : State p} {s : Nat} {r : Tp}
    {lo hi : U s} {body : Tp.denote p (.u s) → Expr (Tp.denote p) r}
    {Q : Option (State p × Tp.denote p .unit) → Prop} :
    lo < hi →
    Omni p Γ st (.letIn (body lo) (fun _ => .loop (lo + 1) hi body)) Q →
    Omni p Γ st (.loop lo hi body) Q

namespace Omni

/-- The postcondition of `Omni` is monotone. -/
theorem consequence {p : Prime} {Γ : Env} {st : State p} {tp : Tp}
    {e : Expr (Tp.denote p) tp}
    {Q Q' : Option (State p × Tp.denote p tp) → Prop} :
    Omni p Γ st e Q →
    (∀ v, Q v → Q' v) →
    Omni p Γ st e Q' := by
  kan_intro h
  kan_intro h_imp
  kan_induction_with h with
  | litField hq => kan_exact Omni.litField (h_imp _ hq)
  | litStr hq => kan_exact Omni.litStr (h_imp _ hq)
  | fmtStr hq => kan_exact Omni.fmtStr (h_imp _ hq)
  | litFalse hq => kan_exact Omni.litFalse (h_imp _ hq)
  | litTrue hq => kan_exact Omni.litTrue (h_imp _ hq)
  | litU hq => kan_exact Omni.litU (h_imp _ hq)
  | litI hq => kan_exact Omni.litI (h_imp _ hq)
  | litUnit hq => kan_exact Omni.litUnit (h_imp _ hq)
  | constFp hq => kan_exact Omni.constFp (h_imp _ hq)
  | constU hq => kan_exact Omni.constU (h_imp _ hq)
  | fn hq => kan_exact Omni.fn (h_imp _ hq)
  | var hq => kan_exact Omni.var (h_imp _ hq)
  | skip hq => kan_exact Omni.skip (h_imp _ hq)
  | iteTrue _ ih => kan_exact Omni.iteTrue (ih h_imp)
  | iteFalse _ ih => kan_exact Omni.iteFalse (ih h_imp)
  | letIn _ _ hN ihE ihB =>
      kan_exact Omni.letIn (ihE (fun _ h => h)) (fun v st' h => ihB v st' h h_imp)
        (fun h => h_imp _ (hN h))
  | callTrait h_eq h_res h_mem hkc htci htco _ ih =>
      kan_exact Omni.callTrait h_eq h_res h_mem hkc htci htco (ih h_imp)
  | callLambda h_eq h_look _ ih =>
      kan_exact Omni.callLambda h_eq h_look (ih h_imp)
  | callDecl h_eq h_mem hkc htci htco _ ih =>
      kan_exact Omni.callDecl h_eq h_mem hkc htci htco (ih h_imp)
  | lam h_all =>
      kan_exact Omni.lam (fun ref hr => h_imp _ (h_all ref hr))
  | callBuiltin hq =>
      kan_refine Omni.callBuiltin (Builtin.conseq _ hq ?_)
      kan_intro r
      kan_intro hr
      kan_exact h_imp _ hr
  | loopDone hge hq => kan_exact Omni.loopDone hge (h_imp _ hq)
  | loopNext hlt _ ih => kan_exact Omni.loopNext hlt (ih h_imp)

/-- The frame rule for `Omni`. -/
theorem frame {p : Prime} {Γ : Env} {tp : Tp} {st₁ st₂ : State p}
    {e : Expr (Tp.denote p) tp}
    {Q : Option (State p × Tp.denote p tp) → Prop} :
    Omni p Γ st₁ e Q →
    LawfulHeap.disjoint st₁ st₂ →
    Omni p Γ (st₁ ∪ st₂) e (fun stv => match stv with
      | some (st', v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st'
      | none => Q none) := by
  kan_intro h
  kan_induction_with h with
  | litField hq =>
      kan_intro hdis
      kan_exact Omni.litField ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | litStr hq =>
      kan_intro hdis
      kan_exact Omni.litStr ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | fmtStr hq =>
      kan_intro hdis
      kan_exact Omni.fmtStr ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | litFalse hq =>
      kan_intro hdis
      kan_exact Omni.litFalse ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | litTrue hq =>
      kan_intro hdis
      kan_exact Omni.litTrue ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | litU hq =>
      kan_intro hdis
      kan_exact Omni.litU ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | litI hq =>
      kan_intro hdis
      kan_exact Omni.litI ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | litUnit hq =>
      kan_intro hdis
      kan_exact Omni.litUnit ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | constFp hq =>
      kan_intro hdis
      kan_exact Omni.constFp ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | constU hq =>
      kan_intro hdis
      kan_exact Omni.constU ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | fn hq =>
      kan_intro hdis
      kan_exact Omni.fn ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | var hq =>
      kan_intro hdis
      kan_exact Omni.var ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | skip hq =>
      kan_intro hdis
      kan_exact Omni.skip ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | iteTrue _ ih =>
      kan_intro hdis
      kan_exact Omni.iteTrue (ih hdis)
  | iteFalse _ ih =>
      kan_intro hdis
      kan_exact Omni.iteFalse (ih hdis)
  | loopDone hge hq =>
      kan_intro hdis
      kan_exact Omni.loopDone hge ⟨_, st₂, hdis, rfl, hq, rfl⟩
  | loopNext hlt _ ih =>
      kan_intro hdis
      kan_exact Omni.loopNext hlt (ih hdis)
  | callDecl h_eq h_mem hkc htci htco _ ih =>
      kan_intro hdis
      kan_exact Omni.callDecl h_eq h_mem hkc htci htco (ih hdis)
  | callTrait h_eq h_res h_mem hkc htci htco _ ih =>
      kan_intro hdis
      kan_exact Omni.callTrait h_eq h_res h_mem hkc htci htco (ih hdis)
  | callLambda h_eq h_look _ ih =>
      kan_intro hdis
      kan_refine Omni.callLambda h_eq ?_ (ih hdis)
      kan_rw [Finmap.lookup_union_left
        (Finmap.mem_of_lookup_eq_some h_look)]
      kan_exact h_look
  | letIn _ _ hN ihE ihB =>
      kan_intro hdis
      kan_exact Omni.letIn (ihE hdis)
        (fun v st' h =>
          let ⟨s₁, s₂, hdis', h_eq, h_q, h_s₂⟩ := h
          h_eq ▸ h_s₂ ▸ ihB v s₁ h_q (h_s₂ ▸ hdis'))
        (fun h => hN h)
  | lam h_all =>
      kan_intro hdis
      kan_apply Omni.lam
      kan_intro r
      kan_intro hr
      kan_refine ⟨_, st₂, ?_, ?_,
        h_all r (fun h_mem => hr (Finmap.mem_union.mpr (Or.inl h_mem))),
        rfl⟩
      · kan_refine ⟨hdis.1, ?_⟩
        kan_rw [Finmap.insert_eq_singleton_union]
        kan_simp_only [Finmap.disjoint_union_left]
        kan_refine ⟨?_, hdis.2⟩
        kan_exact Finmap.singleton_disjoint_of_not_mem
          (fun h_mem => hr (Finmap.mem_union.mpr (Or.inr h_mem)))
      · kan_simp_only [State.union_parts_left, State.mk.injEq,
          Finmap.insert_union]
        kan_exact ⟨rfl, rfl⟩
  | @callBuiltin st' argTps' outTp' b args' Q' hq =>
      kan_intro hdis
      kan_apply Omni.callBuiltin
      kan_apply Builtin.conseq _ (Builtin.frame _ hq hdis.1)
      kan_intro r
      kan_cases_with r with
      | none => kan_intro hr; kan_exact hr
      | some pair =>
          kan_cases_with pair with
          | mk vals val =>
              kan_intro hr
              let ⟨s₁, s₂', hdis_s, h_eq, h_q, h_s₂⟩ := hr
              kan_refine ⟨⟨s₁, st'.lambdas⟩, st₂, ?_, ?_, h_q, rfl⟩
              · kan_exact ⟨h_s₂ ▸ hdis_s, hdis.2⟩
              · kan_simp_only [State.union_parts, State.mk.injEq]
                kan_exact ⟨h_s₂ ▸ h_eq, rfl⟩

/-- `Omni` is monotone in the environment. -/
theorem is_mono {p : Prime} {Γ₁ Γ₂ : Env} {st : State p} {tp : Tp}
    {expr : Expr (Tp.denote p) tp}
    {Q : Option (State p × Tp.denote p tp) → Prop}
    (inner_sub_outer : Γ₁ ⊆ Γ₂) :
    Omni p Γ₁ st expr Q → Omni p Γ₂ st expr Q := by
  kan_intro h
  kan_induction_with h with
  | litField hq => kan_exact Omni.litField hq
  | litStr hq => kan_exact Omni.litStr hq
  | fmtStr hq => kan_exact Omni.fmtStr hq
  | litFalse hq => kan_exact Omni.litFalse hq
  | litTrue hq => kan_exact Omni.litTrue hq
  | litU hq => kan_exact Omni.litU hq
  | litI hq => kan_exact Omni.litI hq
  | litUnit hq => kan_exact Omni.litUnit hq
  | constFp hq => kan_exact Omni.constFp hq
  | constU hq => kan_exact Omni.constU hq
  | fn hq => kan_exact Omni.fn hq
  | var hq => kan_exact Omni.var hq
  | skip hq => kan_exact Omni.skip hq
  | iteTrue _ ih => kan_exact Omni.iteTrue ih
  | iteFalse _ ih => kan_exact Omni.iteFalse ih
  | letIn _ _ hN ihE ihB =>
      kan_exact Omni.letIn ihE (fun v st' h => ihB v st' h) (fun h => hN h)
  | callTrait h_eq h_res h_mem hkc htci htco _ ih =>
      kan_exact Omni.callTrait h_eq
        (TraitResolution.env_mono inner_sub_outer h_res) h_mem hkc htci htco ih
  | callLambda h_eq h_look _ ih =>
      kan_exact Omni.callLambda h_eq h_look ih
  | callDecl h_eq h_mem hkc htci htco _ ih =>
      kan_exact Omni.callDecl h_eq (inner_sub_outer.1 h_mem) hkc htci htco ih
  | lam h_all => kan_exact Omni.lam h_all
  | callBuiltin hq => kan_exact Omni.callBuiltin hq
  | loopDone hge hq => kan_exact Omni.loopDone hge hq
  | loopNext hlt _ ih => kan_exact Omni.loopNext hlt ih

end Omni

end KanLampe
