import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Memory

Port of `Lampe.Builtin.Memory`.  Reference builtins (`ref`, `readRef`,
`writeRef`) and the total `zeroed` builtin that constructs the zero
value of any Noir type.
-/

namespace KanLampe.Builtin

inductive refOmni : Omni where
| mk {P st tp Q v} :
    (∀ ref, ref ∉ st → Q (some (st.insert ref ⟨tp, v⟩, ref))) →
    refOmni P st [tp] (tp.ref) h![v] Q

def ref : Builtin := {
  omni := refOmni
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
      | mk h_mk =>
          kan_exact refOmni.mk (fun r hr => h_imp _ (h_mk r hr))
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
      | mk h_mk =>
          kan_apply refOmni.mk
          kan_intro r
          kan_intro hr
          kan_simp_only [Finmap.mem_union, not_or] at hr
          kan_refine ⟨_, st₂, ?_, ?_, h_mk r hr.1, rfl⟩
          · kan_simp_all [LawfulHeap.disjoint,
              Finmap.disjoint_union_left,
              Finmap.singleton_disjoint_iff_not_mem,
              Finmap.insert_eq_singleton_union]
          · kan_simp [Finmap.insert_union]
}

inductive readRefOmni : Omni where
| mk {P st tp Q ref} {v : Tp.denote P tp} :
    st.lookup ref = some ⟨tp, v⟩ → Q (some (st, v)) →
    readRefOmni P st [tp.ref] tp h![ref] Q

def readRef : Builtin := {
  omni := readRefOmni
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
      | mk h_lookup h_Q =>
          kan_exact readRefOmni.mk h_lookup (h_imp _ h_Q)
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
      | mk h_lookup h_Q =>
          kan_apply readRefOmni.mk
          · kan_rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some h_lookup)]
            kan_exact h_lookup
          · kan_exact ⟨st₁, st₂, hdis, rfl, h_Q, rfl⟩
}

inductive writeRefOmni : Omni where
| mk {P st tp Q ref} {v : Tp.denote P tp} :
    ref ∈ st →
    Q (some (st.insert ref ⟨tp, v⟩, ())) →
    writeRefOmni P st [tp.ref, tp] .unit h![ref, v] Q

def writeRef : Builtin := {
  omni := writeRefOmni
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
      | mk h_mem h_Q =>
          kan_exact writeRefOmni.mk h_mem (h_imp _ h_Q)
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
      | mk h_mem h_Q =>
          kan_apply writeRefOmni.mk
          · kan_exact Finmap.mem_union.mpr (Or.inl h_mem)
          · kan_refine ⟨st₁.insert _ ⟨_, _⟩, st₂, ?_, ?_, h_Q, rfl⟩
            · kan_simp_all [LawfulHeap.disjoint,
                Finmap.disjoint_union_left,
                Finmap.insert_eq_singleton_union,
                Finmap.singleton_disjoint_iff_not_mem]
              kan_exact hdis _ h_mem
            · kan_simp [Finmap.insert_union]
}

/-- `() ↦ 0 : tp`.  Produces the zero value of any Noir type. -/
def zeroed := newGenericTotalPureBuiltin
  (fun (a : Tp) => ⟨[], a⟩)
  (fun {p} a _ => Tp.zero p a)

end KanLampe.Builtin
