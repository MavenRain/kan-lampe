import KanLampe.Ast
import KanLampe.Tp
import KanLampe.Semantics
import KanLampe.SeparationLogic.LawfulHeap
import KanLampe.Builtin.Memory

/-!
# KanLampe.Hoare.Total

Port of `Lampe.Hoare.Total`.  Defines the total Hoare triple `THoare`
together with `consequence`, `var_intro`, `letIn_intro`, and the
builtin-intro rules for reference and `fresh` operations.
-/

namespace KanLampe

def THoare
    {tp : Tp}
    (p : Prime)
    (Γ : Env)
    (P : SLP (State p))
    (e : Expr (Tp.denote p) tp)
    (Q : (tp.denote p) → SLP (State p)) : Prop :=
  ∀ st, P st → Omni p Γ st e (fun r => match r with
    | none => True
    | some (st', v) => Q v st')

namespace THoare

theorem consequence {p : Prime} {Γ : Env} {tp : Tp}
    {e : Expr (Tp.denote p) tp}
    {H₁ H₂ : SLP (State p)}
    {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_pre_conseq : H₂ ⊢ H₁)
    (h_hoare : THoare p Γ H₁ e Q₁)
    (h_post_conseq : ∀ v, Q₁ v ⊢ Q₂ v) :
    THoare p Γ H₂ e Q₂ := by
  kan_intro st
  kan_intro h
  kan_exact Omni.consequence (h_hoare st (h_pre_conseq st h))
    (fun r => match r with
      | none => fun hr => hr
      | some (st', v) => fun hr => h_post_conseq v st' hr)

theorem var_intro {p : Prime} {Γ : Env} {tp : Tp} {v : Tp.denote p tp}
    {P : Tp.denote p tp → SLP (State p)} :
    THoare p Γ (P v) (.var v) P := by
  kan_intro st
  kan_intro h
  kan_exact Omni.var h

theorem letIn_intro {p : Prime} {Γ : Env} {tp₁ tp₂ : Tp}
    {e₁ : Expr (Tp.denote p) tp₁}
    {e₂ : Tp.denote p tp₁ → Expr (Tp.denote p) tp₂}
    {H : SLP (State p)}
    {P : Tp.denote p tp₁ → SLP (State p)}
    {Q : Tp.denote p tp₂ → SLP (State p)}
    (h₁ : THoare p Γ H e₁ P)
    (h₂ : ∀ v, THoare p Γ (P v) (e₂ v) Q) :
    THoare p Γ H (.letIn e₁ e₂) Q := by
  kan_intro st
  kan_intro h
  kan_exact Omni.letIn (h₁ st h)
    (fun v st' hq => h₂ v st' hq)
    (fun hn => hn)

theorem ref_intro {p : Prime} {Γ : Env} {tp : Tp} {v : Tp.denote p tp}
    {P : Tp.denote p tp.ref → SLP (State p)} :
    THoare p Γ
      (fun st => ∀ r, r ∉ st →
        P r ⟨st.vals.insert r ⟨tp, v⟩, st.lambdas⟩)
      (.callBuiltin [tp] tp.ref Builtin.ref h![v])
      P := by
  kan_intro st
  kan_intro h
  kan_exact Omni.callBuiltin (Builtin.refOmni.mk (fun r hr => h r hr))

theorem readRef_intro {p : Prime} {Γ : Env} {tp : Tp} {v : Tp.denote p tp}
    {ref : Ref} {P : Tp.denote p tp → SLP (State p)} :
    THoare p Γ
      (fun st => st.vals.lookup ref = some ⟨tp, v⟩ ∧ P v st)
      (.callBuiltin [tp.ref] tp Builtin.readRef h![ref])
      P := by
  kan_intro st
  kan_intro h
  kan_exact Omni.callBuiltin (Builtin.readRefOmni.mk h.1 h.2)

theorem writeRef_intro {p : Prime} {Γ : Env} {tp : Tp}
    {ref : Ref} {v : Tp.denote p tp}
    {P : Tp.denote p .unit → SLP (State p)} :
    THoare p Γ
      (fun st => ref ∈ st ∧
        P () ⟨st.vals.insert ref ⟨tp, v⟩, st.lambdas⟩)
      (.callBuiltin [tp.ref, tp] .unit Builtin.writeRef h![ref, v])
      P := by
  kan_intro st
  kan_intro h
  kan_exact Omni.callBuiltin (Builtin.writeRefOmni.mk h.1 h.2)

theorem fresh_intro {p : Prime} {Γ : Env} {tp : Tp}
    {P : Tp.denote p tp → SLP (State p)} :
    THoare p Γ
      (SLP.forall' P)
      (.callBuiltin [] tp Builtin.fresh h![])
      P := by
  kan_intro st
  kan_intro h
  kan_exact Omni.callBuiltin (Builtin.freshOmni.mk (fun v => h v))

end THoare

end KanLampe
