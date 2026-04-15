import KanLampe.Ast

/-!
# KanLampe.Semantics.Env

Port of `Lampe.Semantics.Env`.  Defines `Env` (in-scope functions and
trait impls) and its subset lattice lemmas.
-/

namespace KanLampe

/-- In-scope functions and trait impls for a Noir program. -/
structure Env where
  functions : List FunctionDecl
  traits : List (Ident × TraitImpl)
deriving Inhabited

namespace Env

/-- `Γᵢ ⊆ Γₒ`: every function / trait impl in `Γᵢ` appears in `Γₒ`. -/
def contains (Γₒ : Env) (Γᵢ : Env) : Prop :=
  (Γᵢ.functions ⊆ Γₒ.functions) ∧ (Γᵢ.traits ⊆ Γₒ.traits)

/-- Component-wise concatenation of two environments. -/
def append (Γₗ : Env) (Γᵣ : Env) : Env :=
  ⟨Γₗ.functions ++ Γᵣ.functions, Γₗ.traits ++ Γᵣ.traits⟩

end Env

instance : Append Env where
  append := Env.append

instance : HasSubset Env where
  Subset left right := right.contains left

namespace Env

@[simp]
lemma functions_append {Γₗ Γᵣ : Env} :
    (Γₗ ++ Γᵣ).functions = Γₗ.functions ++ Γᵣ.functions := rfl

@[simp]
lemma traits_append {Γₗ Γᵣ : Env} :
    (Γₗ ++ Γᵣ).traits = Γₗ.traits ++ Γᵣ.traits := rfl

@[trans]
lemma subset_trans {Γ₁ Γ₂ Γ₃ : Env} : Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃ := by
  kan_intro h₁₂
  kan_intro h₂₃
  kan_exact ⟨List.Subset.trans h₁₂.1 h₂₃.1, List.Subset.trans h₁₂.2 h₂₃.2⟩

@[simp]
lemma subset_refl {Γ : Env} : Γ ⊆ Γ :=
  ⟨List.Subset.refl _, List.Subset.refl _⟩

@[simp]
lemma subset_append_left {Γₗ Γᵣ : Env} : Γₗ ⊆ Γₗ ++ Γᵣ :=
  ⟨List.subset_append_left _ _, List.subset_append_left _ _⟩

@[simp]
lemma subset_append_right {Γₗ Γᵣ : Env} : Γᵣ ⊆ Γₗ ++ Γᵣ :=
  ⟨List.subset_append_right _ _, List.subset_append_right _ _⟩

@[simp]
lemma subset_append_of_subset_left {Γᵢ Γₗ Γᵣ : Env} :
    Γᵢ ⊆ Γₗ → Γᵢ ⊆ Γₗ ++ Γᵣ := by
  kan_intro h
  kan_exact subset_trans h subset_append_left

@[simp]
lemma subset_append_of_subset_right {Γᵢ Γₗ Γᵣ : Env} :
    Γᵢ ⊆ Γᵣ → Γᵢ ⊆ Γₗ ++ Γᵣ := by
  kan_intro h
  kan_exact subset_trans h subset_append_right

@[simp]
lemma append_subset_iff {Γ₁ Γ₂ Γ₃ : Env} :
    Γ₁ ++ Γ₂ ⊆ Γ₃ ↔ Γ₁ ⊆ Γ₃ ∧ Γ₂ ⊆ Γ₃ := by
  kan_constructor
  · kan_intro h
    kan_exact ⟨subset_trans subset_append_left h,
               subset_trans subset_append_right h⟩
  · kan_intro h
    kan_exact ⟨List.append_subset.mpr ⟨h.1.1, h.2.1⟩,
               List.append_subset.mpr ⟨h.1.2, h.2.2⟩⟩

@[simp]
lemma subset_mono_left {Γᵢ Γₗ Γᵣ : Env} :
    Γᵢ ⊆ Γₗ → Γᵢ ++ Γᵣ ⊆ Γₗ ++ Γᵣ := by
  kan_intro h
  kan_exact append_subset_iff.mpr
    ⟨subset_trans h subset_append_left, subset_append_right⟩

@[simp]
lemma subset_mono_right {Γᵢ Γₗ Γᵣ : Env} :
    Γᵢ ⊆ Γᵣ → Γᵣ ++ Γᵢ ⊆ Γₗ ++ Γᵣ := by
  kan_intro h
  kan_exact append_subset_iff.mpr
    ⟨subset_append_right, subset_trans h subset_append_right⟩

end Env

end KanLampe
