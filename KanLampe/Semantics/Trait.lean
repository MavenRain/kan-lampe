import KanLampe.Semantics.Env

/-!
# KanLampe.Semantics.Trait

Port of `Lampe.Semantics.Trait`.  Trait resolvability and trait
resolution predicates, and their environment-monotonicity lemmas.
-/

namespace KanLampe

/-- Indicates that in environment `Γ` a trait implementation matching
the provided `TraitImplRef` can be resolved. -/
inductive TraitResolvable (Γ : Env) : TraitImplRef → Prop where
| ok {ref : TraitImplRef} {impl : TraitImpl} :
    (ref.trait.name, impl) ∈ Γ.traits →
    (ktc : ref.trait.traitGenericKinds = impl.traitGenericKinds) →
    (implGenerics : HList Kind.denote impl.implGenericKinds) →
    (ktc ▸ ref.trait.traitGenerics = impl.traitGenerics implGenerics) →
    ref.self = impl.self implGenerics →
    (∀ constraint ∈ impl.constraints implGenerics,
        TraitResolvable Γ constraint) →
    TraitResolvable Γ ref

/-- `TraitResolvable` is monotone in the environment. -/
theorem TraitResolvable.env_mono
    {Γ₁ Γ₂ : Env} {t : TraitImplRef}
    (inner_sub_outer : Γ₁ ⊆ Γ₂) :
    TraitResolvable Γ₁ t → TraitResolvable Γ₂ t := by
  kan_intro h
  kan_induction_with h with
  | ok h_mem ktc implGenerics h_tg h_self h_cs ih =>
      kan_exact TraitResolvable.ok
        (inner_sub_outer.2 h_mem) ktc implGenerics h_tg h_self
        (fun c hc => ih c hc)

/-- Successful trait resolution yielding the trait's method list. -/
inductive TraitResolution (Γ : Env) : TraitImplRef → List (Ident × Function) → Prop where
| ok {ref : TraitImplRef} {impl : TraitImpl}
    (h_mem : (ref.trait.name, impl) ∈ Γ.traits)
    (ktc : ref.trait.traitGenericKinds = impl.traitGenericKinds)
    (implGenerics : HList Kind.denote impl.implGenericKinds)
    (_ : ktc ▸ ref.trait.traitGenerics = impl.traitGenerics implGenerics)
    (_ : ref.self = impl.self implGenerics)
    (_ : ∀ constraint ∈ impl.constraints implGenerics,
        TraitResolvable Γ constraint) :
    TraitResolution Γ ref (impl.impl implGenerics)

/-- `TraitResolution` is monotone in the environment. -/
theorem TraitResolution.env_mono
    {Γ₁ Γ₂ : Env} {t : TraitImplRef} {xs : List (Ident × Function)}
    (inner_sub_outer : Γ₁ ⊆ Γ₂) :
    TraitResolution Γ₁ t xs → TraitResolution Γ₂ t xs := by
  kan_intro h
  kan_cases_with h with
  | ok h_mem ktc implGenerics h_tg h_self h_cs =>
      kan_exact TraitResolution.ok
        (inner_sub_outer.2 h_mem) ktc implGenerics h_tg h_self
        (fun c hc => TraitResolvable.env_mono inner_sub_outer (h_cs c hc))

end KanLampe
