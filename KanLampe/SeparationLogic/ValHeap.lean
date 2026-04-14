import Mathlib.Data.Finmap
import KanLampe.SeparationLogic.LawfulHeap
import KanLampe.SeparationLogic.SLP
import KanLampe.Tp

/-!
# KanLampe.SeparationLogic.ValHeap

Port of `Lampe.SeparationLogic.ValHeap`.  Defines `ValHeap p` as a
`Finmap` from `Ref` to `AnyValue p`, and installs a `LawfulHeap`
instance.  All proofs use kan-tactics only.
-/

lemma Finmap.insert_eq_singleton_union {α : Type _} {β : α → Type _} [DecidableEq α]
    {ref : α} {v : β ref} {m : Finmap β} :
    m.insert ref v = Finmap.singleton ref v ∪ m := by
  kan_rfl

@[simp]
lemma Finmap.singleton_disjoint_of_not_mem {α : Type _} {β : α → Type _} [DecidableEq α]
    {ref : α} {v : β ref} {s : Finmap β} (hp : ref ∉ s) :
    Finmap.Disjoint (Finmap.singleton ref v) s := by
  kan_simp_all [Finmap.Disjoint]

lemma Finmap.singleton_disjoint_iff_not_mem {α : Type _} {β : α → Type _} [DecidableEq α]
    {ref : α} {v : β ref} {s : Finmap β} :
    Finmap.Disjoint (Finmap.singleton ref v) s ↔ (ref ∉ s) := by
  kan_simp_all [Finmap.Disjoint]

theorem Finmap.union_self {α : Type _} {β : Type _} [DecidableEq α]
    {a : Finmap fun _ : α => β} : a ∪ a = a := by
  kan_apply Finmap.ext_lookup
  kan_intro x
  kan_by_cases h : x ∈ a
  · kan_rw [Finmap.lookup_union_left h]
  · kan_rw [Finmap.lookup_union_left_of_not_in h]

namespace KanLampe

def AnyValue (p : Prime) := (tp : Tp) × tp.denote p

abbrev ValHeap (p : Prime) := Finmap (fun (_ : Ref) => AnyValue p)

instance {p : Prime} : LawfulHeap (ValHeap p) where
  union := fun a b => a ∪ b
  disjoint := fun a b => a.Disjoint b
  empty := ∅
  thm_union_empty := Finmap.union_empty
  thm_union_assoc := Finmap.union_assoc
  thm_disjoint_symm_iff := Finmap.Disjoint.symm_iff _ _
  thm_union_comm_of_disjoint := Finmap.union_comm_of_disjoint
  thm_disjoint_union_left := Finmap.disjoint_union_left
  thm_disjoint_empty := Finmap.disjoint_empty

end KanLampe
