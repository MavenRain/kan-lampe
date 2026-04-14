import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use
import KanLampe.Data.Field
import KanLampe.Tactic.IntroCases
import KanLampe.SeparationLogic.LawfulHeap

namespace KanLampe

universe u v

variable {α β : Type _}

def SLP (α : Type _) [LawfulHeap α] := α → Prop

namespace SLP

def star [LawfulHeap α] (lhs rhs : SLP α) : SLP α := fun st =>
  ∃ st₁ st₂, LawfulHeap.disjoint st₁ st₂ ∧ st = st₁ ∪ st₂ ∧ lhs st₁ ∧ rhs st₂

def lift [LawfulHeap α] (pr : Prop) : SLP α := fun st => pr ∧ st = ∅

def wand [LawfulHeap α] (lhs rhs : SLP α) : SLP α :=
  fun st => ∀ st', LawfulHeap.disjoint st st' → lhs st' → rhs (st ∪ st')

def top [LawfulHeap α] : SLP α := fun _ => True

def entails [LawfulHeap α] (a b : SLP α) := ∀ st, a st → b st

def forall' [LawfulHeap α] (f : β → SLP α) : SLP α := fun st => ∀ v, f v st
def exists' [LawfulHeap α] (f : β → SLP α) : SLP α := fun st => ∃ v, f v st

instance [LawfulHeap α] : Coe Prop (SLP α) := ⟨lift⟩

notation:max "⊤" => top

notation:max "⟦" x "⟧" => lift x

notation:max "⟦⟧" => ⟦True⟧

infixr:35 " ⋆ " => star

infixr:30 " -⋆ " => wand

infix:10 " ⊢ " => entails

open Lean.TSyntax.Compat in
macro "∃∃" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``exists' xs b

@[app_unexpander exists'] def unexpandExists' : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃ $xs:binderIdent*, $b) => `(∃∃  $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∃∃ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∃∃ ($x:ident : $t), $b)
  | _                                              => throw ()

open Lean.TSyntax.Compat in
macro "∀∀" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders ``forall' xs b

@[app_unexpander forall'] def unexpandForAll' : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∃ $xs:binderIdent*, $b) => `(∀∀  $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∀∀ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∀∀ ($x:ident : $t), $b)
  | _                                              => throw ()

theorem entails_trans [LawfulHeap α] {P Q R : SLP α} : (P ⊢ Q) → (Q ⊢ R) → (P ⊢ R) := by
  kan_intro hPQ
  kan_intro hQR
  kan_intro st
  kan_intro hP
  kan_exact hQR st (hPQ st hP)

section basic

theorem eq_of_iff [LawfulHeap α] {P Q : SLP α} : (P ⊢ Q) → (Q ⊢ P) → P = Q := by
  kan_intro hPQ
  kan_intro hQP
  kan_apply funext
  kan_intro st
  kan_apply eq_iff_iff.mpr
  kan_apply Iff.intro
  · kan_exact hPQ st
  · kan_exact hQP st

theorem exists_pure [LawfulHeap α] {P : β → Prop} :
    (SLP.exists' fun x => ⟦P x⟧) = SLP.lift (α := α) (∃ x, P x) := by
  (kan_unfold SLP.exists' SLP.lift)
  kan_simp

theorem exists_intro_l [LawfulHeap α] {H : β → SLP α} {Q : SLP α} :
    (∀ a, (H a ⊢ Q)) → ((∃∃ a, H a) ⊢ Q) := by
  kan_intro h
  kan_intro st
  (kan_rintro ⟨v, hH⟩)
  kan_exact h v st hH

theorem exists_intro_r [LawfulHeap α] {H : SLP α} {Q : β → SLP α} {a} :
    (H ⊢ Q a) → (H ⊢ ∃∃ a, Q a) := by
  kan_intro h
  kan_intro st
  kan_intro hH
  (kan_unfold SLP.exists')
  kan_exact ⟨a, h st hH⟩

@[simp]
theorem apply_top [LawfulHeap α] {st : α} : ⊤ st := by
  kan_exact True.intro

theorem forall_left [LawfulHeap β] {P : α → SLP β} {Q : SLP β} {a : α} :
    (P a ⊢ Q) → ((∀∀ (a : α), P a) ⊢ Q) := by
  (kan_unfold forall')
  kan_intro h
  kan_intro st
  kan_intro hall
  kan_exact h st (hall a)

theorem forall_right [LawfulHeap β] {H : SLP β} {H' : α → SLP β} :
    (∀ x, H ⊢ H' x) → (H ⊢ ∀∀ x, H' x) := by
  (kan_unfold forall' entails)
  kan_intro h
  kan_intro st
  kan_intro hH
  kan_intro v
  kan_exact h v st hH

theorem pure_left [LawfulHeap β] {H H' : SLP β} {P : Prop} :
    (P → (H ⊢ H')) → (P ⋆ H ⊢ H') := by
  (kan_unfold star entails lift)
  kan_intro hpH
  kan_intro st
  (kan_rintro ⟨st₁, st₂, hdis, heq, ⟨hP, heq₁⟩, hH⟩)
  kan_subst heq₁
  kan_subst heq
  kan_simp
  kan_exact hpH hP st₂ hH

theorem pure_left' [LawfulHeap α] {H : SLP α} {P : Prop} :
    (P → (⟦⟧ ⊢ H)) → (P ⊢ H) := by
  (kan_unfold entails lift)
  kan_intro h
  kan_intro st
  (kan_rintro ⟨hP, hemp⟩)
  kan_exact h hP st ⟨True.intro, hemp⟩

theorem pure_right [LawfulHeap α] {H₁ H₂ : SLP α} {P : Prop} :
    P → (H₁ ⊢ H₂) → (H₁ ⊢ P ⋆ H₂) := by
  (kan_unfold star entails lift)
  kan_intro hP
  kan_intro hH
  kan_intro st
  kan_intro hst
  kan_refine ⟨∅, st, ?_, ?_, ?_, ?_⟩
  · kan_exact LawfulHeap.empty_disjoint
  · kan_simp
  · kan_exact ⟨hP, rfl⟩
  · kan_exact hH st hst

theorem entails_self [LawfulHeap α] {H : SLP α} : H ⊢ H := by
  kan_intro st
  kan_intro h
  kan_exact h

theorem entails_top [LawfulHeap α] {H : SLP α} : H ⊢ ⊤ := by
  kan_intro st
  kan_intro hH
  kan_exact True.intro

@[simp]
theorem forall_unused [LawfulHeap β] {α : Type u} [Inhabited α] {P : SLP β} :
    (∀∀ (_ : α), P) = P := by
  kan_apply funext
  kan_intro st
  (kan_unfold forall')
  kan_rw [eq_iff_iff]
  kan_apply Iff.intro
  · kan_intro h
    kan_exact h Inhabited.default
  · kan_intro hP
    kan_intro x
    kan_exact hP

end basic

section star

theorem star_comm [LawfulHeap α] {G H : SLP α} : (G ⋆ H) = (H ⋆ G) := by
  kan_apply funext
  kan_intro st
  kan_apply eq_iff_iff.mpr
  kan_apply Iff.intro
  · (kan_rintro ⟨s₁, s₂, hdis, heq, hG, hH⟩)
    kan_exact ⟨s₂, s₁,
      LawfulHeap.disjoint_symm_iff.mp hdis,
      heq.trans (LawfulHeap.union_comm_of_disjoint_ hdis),
      hH, hG⟩
  · (kan_rintro ⟨s₁, s₂, hdis, heq, hH, hG⟩)
    kan_exact ⟨s₂, s₁,
      LawfulHeap.disjoint_symm_iff.mp hdis,
      heq.trans (LawfulHeap.union_comm_of_disjoint_ hdis),
      hG, hH⟩

@[simp]
theorem true_star [LawfulHeap α] {H : SLP α} : (⟦⟧ ⋆ H) = H := by
  kan_apply funext
  kan_intro st
  kan_rw [eq_iff_iff]
  (kan_unfold lift star)
  kan_apply Iff.intro
  · (kan_rintro ⟨s₁, s₂, hdis, heq, ⟨_, hemp⟩, hH⟩)
    kan_subst hemp
    kan_subst heq
    kan_rw [LawfulHeap.empty_union]
    kan_exact hH
  · kan_intro hH
    kan_exact ⟨∅, st, LawfulHeap.empty_disjoint, LawfulHeap.empty_union.symm,
      ⟨True.intro, rfl⟩, hH⟩

@[simp]
theorem star_true [LawfulHeap α] {H : SLP α} : (H ⋆ ⟦⟧) = H := by
  kan_rw [star_comm]
  kan_exact true_star

@[simp]
theorem star_assoc [LawfulHeap α] {F G H : SLP α} : ((F ⋆ G) ⋆ H) = (F ⋆ G ⋆ H) := by
  kan_apply funext
  kan_intro st
  kan_rw [eq_iff_iff]
  (kan_unfold star)
  kan_apply Iff.intro
  · (kan_rintro ⟨s₁₂, s₃, hd₁, heq₁, ⟨s₁, s₂, hd₂, heq₂, hF, hG⟩, hH⟩)
    kan_subst heq₂
    kan_have hdp : LawfulHeap.disjoint s₁ s₃ ∧ LawfulHeap.disjoint s₂ s₃ :=
      (LawfulHeap.disjoint_union_left s₁ s₂ s₃).mp hd₁
    kan_exact ⟨s₁, s₂ ∪ s₃,
      (LawfulHeap.disjoint_union_right s₁ s₂ s₃).mpr ⟨hd₂, hdp.1⟩,
      heq₁.trans LawfulHeap.union_assoc,
      hF, s₂, s₃, hdp.2, rfl, hG, hH⟩
  · (kan_rintro ⟨s₁, s₂₃, hd₁, heq₁, hF, s₂, s₃, hd₂, heq₂, hG, hH⟩)
    kan_subst heq₂
    kan_have hdp : LawfulHeap.disjoint s₁ s₂ ∧ LawfulHeap.disjoint s₁ s₃ :=
      (LawfulHeap.disjoint_union_right s₁ s₂ s₃).mp hd₁
    kan_exact ⟨s₁ ∪ s₂, s₃,
      (LawfulHeap.disjoint_union_left s₁ s₂ s₃).mpr ⟨hdp.2, hd₂⟩,
      heq₁.trans LawfulHeap.union_assoc.symm,
      ⟨s₁, s₂, hdp.1, rfl, hF, hG⟩, hH⟩

@[simp]
theorem ent_star_top [LawfulHeap α] {H : SLP α} : H ⊢ H ⋆ ⊤ := by
  kan_intro st
  kan_intro hH
  kan_refine ⟨st, ∅, ?_, ?_, hH, True.intro⟩
  · kan_rw [LawfulHeap.disjoint_symm_iff]
    kan_exact LawfulHeap.empty_disjoint
  · kan_rw [LawfulHeap.union_empty]

theorem star_mono_r [LawfulHeap α] {P Q R : SLP α} : (P ⊢ Q) → (P ⋆ R ⊢ Q ⋆ R) := by
  (kan_unfold star entails)
  kan_intro hPQ
  kan_intro st
  (kan_rintro ⟨s₁, s₂, hdis, heq, hP, hR⟩)
  kan_exact ⟨s₁, s₂, hdis, heq, hPQ s₁ hP, hR⟩

theorem star_mono_l [LawfulHeap α] {P Q R : SLP α} : (P ⊢ Q) → (R ⋆ P ⊢ R ⋆ Q) := by
  (kan_unfold star entails)
  kan_intro hPQ
  kan_intro st
  (kan_rintro ⟨s₁, s₂, hdis, heq, hR, hP⟩)
  kan_exact ⟨s₁, s₂, hdis, heq, hR, hPQ s₂ hP⟩

theorem star_mono_l' [LawfulHeap α] {P Q : SLP α} : (⟦⟧ ⊢ Q) → (P ⊢ P ⋆ Q) := by
  (kan_unfold star entails lift)
  kan_intro h
  kan_intro st
  kan_intro hP
  kan_refine ⟨st, ∅, ?_, ?_, hP, h ∅ ⟨True.intro, rfl⟩⟩
  · kan_rw [LawfulHeap.disjoint_symm_iff]
    kan_exact LawfulHeap.empty_disjoint
  · kan_rw [LawfulHeap.union_empty]

theorem star_mono [LawfulHeap α] {H₁ H₂ Q₁ Q₂ : SLP α} :
    (H₁ ⊢ H₂) → (Q₁ ⊢ Q₂) → (H₁ ⋆ Q₁ ⊢ H₂ ⋆ Q₂) := by
  (kan_unfold star entails)
  kan_intro h₁
  kan_intro h₂
  kan_intro st
  (kan_rintro ⟨s₁, s₂, hdis, heq, hH, hQ⟩)
  kan_exact ⟨s₁, s₂, hdis, heq, h₁ s₁ hH, h₂ s₂ hQ⟩

theorem forall_star [LawfulHeap α] {P : α → SLP α} {Q : SLP α} :
    (∀∀ x, P x) ⋆ Q ⊢ ∀∀ x, P x ⋆ Q := by
  (kan_unfold star forall' entails)
  kan_intro st
  (kan_rintro ⟨s₁, s₂, hdis, heq, hall, hQ⟩)
  kan_intro v
  kan_exact ⟨s₁, s₂, hdis, heq, hall v, hQ⟩

theorem star_forall [LawfulHeap β] {P : α → SLP β} {Q : SLP β} :
    Q ⋆ (∀∀ x, P x) ⊢ ∀∀ x, Q ⋆ P x := by
  (kan_unfold star forall' entails)
  kan_intro st
  (kan_rintro ⟨s₁, s₂, hdis, heq, hQ, hall⟩)
  kan_intro v
  kan_exact ⟨s₁, s₂, hdis, heq, hQ, hall v⟩

@[simp]
theorem top_star_top [LawfulHeap α] : (top ⋆ (⊤ : SLP α)) = (⊤ : SLP α) := by
  kan_apply funext
  kan_intro x
  kan_apply eq_iff_iff.mpr
  kan_apply Iff.intro
  · kan_intro _h
    kan_exact True.intro
  · kan_intro _h
    kan_exact ⟨∅, x, LawfulHeap.empty_disjoint, LawfulHeap.empty_union.symm,
      True.intro, True.intro⟩

theorem ent_drop_left [LawfulHeap α] {Q H : SLP α} : Q ⋆ H ⊢ Q ⋆ ⊤ := by
  (kan_unfold star entails)
  kan_intro st
  (kan_rintro ⟨s₁, s₂, hdis, heq, hQ, _⟩)
  kan_exact ⟨s₁, s₂, hdis, heq, hQ, True.intro⟩

end star

section wand

@[simp]
theorem wand_self_star [LawfulHeap α] {H : SLP α} : (H -⋆ H ⋆ top) = top := by
  kan_apply funext
  kan_intro st
  kan_apply eq_iff_iff.mpr
  kan_apply Iff.intro
  · kan_intro hw
    kan_exact True.intro
  · kan_intro ht
    kan_intro st'
    kan_intro hdis
    kan_intro hH
    kan_exact ⟨st', st,
      LawfulHeap.disjoint_symm_iff.mp hdis,
      LawfulHeap.union_comm_of_disjoint_ hdis,
      hH, True.intro⟩

theorem wand_intro [LawfulHeap α] {A B C : SLP α} : (A ⋆ B ⊢ C) → (A ⊢ B -⋆ C) := by
  (kan_unfold wand star entails)
  kan_intro hABC
  kan_intro st
  kan_intro hA
  kan_intro st'
  kan_intro hdis
  kan_intro hB
  kan_exact hABC (st ∪ st') ⟨st, st', hdis, rfl, hA, hB⟩

theorem wand_cancel [LawfulHeap α] {P Q : SLP α} : (P ⋆ (P -⋆ Q)) ⊢ Q := by
  (kan_unfold star wand entails)
  kan_intro st
  (kan_rintro ⟨s₁, s₂, hdis, heq, hP, hPQ⟩)
  kan_subst heq
  kan_rw [LawfulHeap.union_comm_of_disjoint_ hdis]
  kan_apply hPQ
  · kan_rw [LawfulHeap.disjoint_symm_iff]
    kan_exact hdis
  · kan_exact hP

end wand

theorem extract_prop [LawfulHeap α] {H₁ H₂ : SLP α} {st : α} {P : Prop}
    (h₁ : (H₁ ⋆ H₂) st) (h₂ : H₁ ⊢ ⟦P⟧ ⋆ ⊤) : P := by
  kan_exact h₁.elim (fun s₁ h =>
    h.elim (fun _ ⟨_, _, hH₁, _⟩ =>
      (h₂ s₁ hH₁).elim (fun _ h' =>
        h'.elim (fun _ ⟨_, _, ⟨hP, _⟩, _⟩ => hP))))

theorem star_exists [LawfulHeap α] {P : SLP α} {Q : β → SLP α} :
    (∃∃ x, Q x ⋆ P) = ((∃∃ x, Q x) ⋆ P) := by
  (kan_unfold SLP.exists' SLP.star)
  kan_apply funext
  kan_intro st
  kan_rw [eq_iff_iff]
  kan_apply Iff.intro
  · (kan_rintro ⟨v, s₁, s₂, hdis, heq, hQ, hP⟩)
    kan_exact ⟨s₁, s₂, hdis, heq, ⟨v, hQ⟩, hP⟩
  · (kan_rintro ⟨s₁, s₂, hdis, heq, ⟨v, hQ⟩, hP⟩)
    kan_exact ⟨v, s₁, s₂, hdis, heq, hQ, hP⟩

theorem exists_star [LawfulHeap α] {P : SLP α} {Q : β → SLP α} :
    (∃∃ x, P ⋆ Q x) = ((∃∃ x, Q x) ⋆ P) := by
  kan_conv_lhs
    arg 1
    ext x
    rw [SLP.star_comm]
  kan_rw [star_exists]

theorem lift_star_lift [LawfulHeap α] {P Q : Prop} :
    (⟦P⟧ ⋆ ⟦Q⟧) = (⟦P ∧ Q⟧ : SLP α) := by
  kan_apply funext
  kan_intro st
  (kan_unfold star lift)
  kan_apply eq_iff_iff.mpr
  kan_apply Iff.intro
  · (kan_rintro ⟨s₁, s₂, _, heq, ⟨hP, hemp₁⟩, ⟨hQ, hemp₂⟩⟩)
    kan_subst hemp₁
    kan_subst hemp₂
    kan_exact ⟨⟨hP, hQ⟩, heq.trans LawfulHeap.empty_union⟩
  · (kan_rintro ⟨⟨hP, hQ⟩, hemp⟩)
    kan_exact ⟨∅, ∅, LawfulHeap.empty_disjoint,
      hemp.trans LawfulHeap.empty_union.symm, ⟨hP, rfl⟩, ⟨hQ, rfl⟩⟩

end SLP

end KanLampe
