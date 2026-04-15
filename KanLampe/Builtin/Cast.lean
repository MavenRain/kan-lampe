import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Cast

Port of `Lampe.Builtin.Cast`.  Defines a `CastTp` type-class with
the castable Noir type pairs, a `castOmni` semantic inductive, and
the `cast` builtin with its `omni_conseq` / `omni_frame` proofs.
-/

namespace KanLampe.Builtin

/-- Represents the Noir types that can be cast into each other. -/
class CastTp (tp tp' : Tp) where
  cast : {p : Prime} → Tp.denote p tp → Tp.denote p tp'

@[simp]
instance {tp : Tp} : CastTp tp tp where
  cast := fun a => a

@[simp]
instance {s₁ s₂ : Nat} : CastTp (.u s₁) (.i s₂) where
  cast := fun a => a.zeroExtend s₂

@[simp]
instance {s₁ s₂ : Nat} : CastTp (.i s₁) (.u s₂) where
  cast := fun a => a.zeroExtend s₂

@[simp]
instance {s₁ s₂ : Nat} : CastTp (.u s₁) (.u s₂) where
  cast := fun a => a.zeroExtend s₂

@[simp]
instance {s₁ s₂ : Nat} : CastTp (.i s₁) (.i s₂) where
  cast := fun a => a.signExtend s₂

@[simp]
instance {s : Nat} : CastTp (.u s) (.field) where
  cast := fun a => a.toNat

@[simp]
instance {s : Nat} : CastTp (.i s) (.field) where
  cast := fun a => a.toNat

@[simp]
instance {s : Nat} : CastTp (.field) (.u s) where
  cast := fun a => a.val

@[simp]
instance {s : Nat} : CastTp (.field) (.i s) where
  cast := fun a => a.val

@[simp]
instance {s : Nat} : CastTp (.bool) (.u s) where
  cast := fun a => if a then 1 else 0

@[simp]
instance {s : Nat} : CastTp (.u s) (.bool) where
  cast := fun a => a ≠ 0

@[simp]
instance {s : Nat} : CastTp (.i s) (.bool) where
  cast := fun a => a ≠ 0

@[simp]
instance : CastTp (.field) (.bool) where
  cast := fun a => a ≠ 0

@[simp]
instance {s : Nat} : CastTp (.bool) (.i s) where
  cast := fun a => if a then 1 else 0

@[simp]
instance : CastTp (.bool) (.field) where
  cast := fun a => if a then 1 else 0

inductive castOmni : Omni where
| ok {P st tp tp' v Q} [CastTp tp tp'] :
    Q (some (st, CastTp.cast v)) → castOmni P st [tp] tp' h![v] Q

def cast : Builtin := {
  omni := castOmni
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
      | ok h_Q => kan_exact castOmni.ok (h_imp _ h_Q)
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
      | ok h_Q => kan_exact castOmni.ok ⟨st₁, st₂, hdis, rfl, h_Q, rfl⟩
}

end KanLampe.Builtin
