import KanLampe.Builtin.Basic
import KanLampe.Lens

/-!
# KanLampe.Builtin.Lens

Port of `Lampe.Builtin.Lens`.  Defines the `modifyLens` and `getLens`
builtins, which execute a `Lens` under the reference heap.
-/

lemma Finmap.insert_mem_disjoint {α : Type _} {β : α → Type _} [DecidableEq α]
    {ref : α} {v : β ref} {m₁ m₂ : Finmap β}
    (hd : m₁.Disjoint m₂) (he : ref ∈ m₁) :
    (m₁.insert ref v).Disjoint m₂ := by
  kan_rw [Finmap.insert_eq_singleton_union]
  kan_have hne : ref ∉ m₂ := hd _ he
  kan_simp_only [Finmap.disjoint_union_left]
  kan_refine ⟨?_, hd⟩
  kan_exact Finmap.singleton_disjoint_of_not_mem hne

namespace KanLampe.Builtin

inductive modifyLensOmni {rep : Tp → Type} {tp₁ tp₂ : Tp}
    (lens : Lens rep tp₁ tp₂) : Omni where
| ok {p st Q ref} {s s' : Tp.denote p tp₁} {v' : Tp.denote p tp₂}
    {hr : rep = Tp.denote p} :
    st.lookup ref = some ⟨tp₁, s⟩ →
    some s' = Lens.modify (hr ▸ lens) s v' →
    Q (some (st.insert ref ⟨tp₁, s'⟩, ())) →
    (modifyLensOmni lens) p st [tp₁.ref, tp₂] .unit h![ref, v'] Q
| err {p st Q ref} {s : Tp.denote p tp₁} {v' : Tp.denote p tp₂}
    {hr : rep = Tp.denote p} :
    st.lookup ref = some ⟨tp₁, s⟩ →
    none = Lens.modify (hr ▸ lens) s v' →
    Q none →
    (modifyLensOmni lens) p st [tp₁.ref, tp₂] .unit h![ref, v'] Q

def modifyLens {rep : Tp → Type} {tp₁ tp₂ : Tp}
    (lens : Lens rep tp₁ tp₂) : Builtin := {
  omni := modifyLensOmni lens
  conseq := by
    kan_intro P
    kan_intro st
    kan_intro argTps
    kan_intro outTp
    kan_intro args
    kan_intro Q
    kan_intro Q'
    kan_intro h_omni
    kan_intro h_imp
    kan_cases_with h_omni with
      | ok h_lookup h_mod h_Q =>
          kan_exact modifyLensOmni.ok h_lookup h_mod (h_imp _ h_Q)
      | err h_lookup h_mod h_Q =>
          kan_exact modifyLensOmni.err h_lookup h_mod (h_imp _ h_Q)
  frame := by
    kan_intro P
    kan_intro st₁
    kan_intro st₂
    kan_intro argTps
    kan_intro outTp
    kan_intro args
    kan_intro Q
    kan_intro h_omni
    kan_intro hdis
    kan_cases_with h_omni with
      | ok h_lookup h_mod h_Q =>
          kan_have h_mem : _ ∈ st₁ := Finmap.mem_of_lookup_eq_some h_lookup
          kan_apply modifyLensOmni.ok
          · kan_rw [Finmap.lookup_union_left h_mem]
            kan_exact h_lookup
          · kan_exact h_mod
          · kan_refine ⟨(st₁.insert _ ⟨tp₁, _⟩), st₂, ?_, ?_, h_Q, rfl⟩
            · kan_exact Finmap.insert_mem_disjoint hdis h_mem
            · kan_simp [Finmap.insert_union]
      | err h_lookup h_mod h_Q =>
          kan_have h_mem : _ ∈ st₁ := Finmap.mem_of_lookup_eq_some h_lookup
          kan_apply modifyLensOmni.err
          · kan_rw [Finmap.lookup_union_left h_mem]
            kan_exact h_lookup
          · kan_exact h_mod
          · kan_exact h_Q
}

inductive getLensOmni {rep : Tp → Type} {tp₁ tp₂ : Tp}
    (lens : Lens rep tp₁ tp₂) : Omni where
| ok {p st Q} {s : Tp.denote p tp₁} {v : Tp.denote p tp₂}
    {hr : rep = Tp.denote p} :
    (some v = Lens.get (hr ▸ lens) s) →
    Q (some (st, v)) →
    (getLensOmni lens) p st [tp₁] tp₂ h![s] Q
| err {p st Q} {s : Tp.denote p tp₁} {hr : rep = Tp.denote p} :
    (none = Lens.get (hr ▸ lens) s) →
    Q none →
    (getLensOmni lens) p st [tp₁] tp₂ h![s] Q

def getLens {rep : Tp → Type} {tp₁ tp₂ : Tp}
    (lens : Lens rep tp₁ tp₂) : Builtin := {
  omni := getLensOmni lens
  conseq := by
    kan_intro P
    kan_intro st
    kan_intro argTps
    kan_intro outTp
    kan_intro args
    kan_intro Q
    kan_intro Q'
    kan_intro h_omni
    kan_intro h_imp
    kan_cases_with h_omni with
      | ok h_get h_Q => kan_exact getLensOmni.ok h_get (h_imp _ h_Q)
      | err h_get h_Q => kan_exact getLensOmni.err h_get (h_imp _ h_Q)
  frame := by
    kan_intro P
    kan_intro st₁
    kan_intro st₂
    kan_intro argTps
    kan_intro outTp
    kan_intro args
    kan_intro Q
    kan_intro h_omni
    kan_intro hdis
    kan_cases_with h_omni with
      | ok h_get h_Q =>
          kan_apply getLensOmni.ok h_get
          kan_exact ⟨st₁, st₂, hdis, rfl, h_Q, rfl⟩
      | err h_get h_Q => kan_exact getLensOmni.err h_get h_Q
}

end KanLampe.Builtin
