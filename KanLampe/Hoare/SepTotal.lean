import KanLampe.Ast
import KanLampe.Hoare.Total
import KanLampe.Semantics
import KanLampe.Tp

/-!
# KanLampe.Hoare.SepTotal

Port of `Lampe.Hoare.SepTotal`.  Defines the affine separation-logic
Hoare triple `STHoare` together with its structural rules and the
standard introduction rules for core expression constructors.
-/

namespace KanLampe

/--
A Hoare triple where the states must be valid under separation logic.
Partial with respect to failure and total with respect to termination.
-/
def STHoare (p : Prime) (Γ : Env) (P : SLP (State p))
    {tp : Tp} (e : Expr (Tp.denote p) tp)
    (Q : Tp.denote p tp → SLP (State p)) : Prop :=
  ∀ H, THoare p Γ (P ⋆ H) e (fun v => ((Q v) ⋆ H) ⋆ ⊤)

/--
Shorthand for a total Hoare triple about a pure generic builtin: the
builtin succeeds whenever its precondition `(desc a args).fst` holds
and yields `(desc a args).snd h`.
-/
abbrev STHoarePureBuiltin {A : Type} (p : Prime) (Γ : Env)
    (b : Builtin)
    {a : A}
    {sgn : A → List Tp × Tp}
    {desc : {p : Prime}
          → (a : A)
          → (args : HList (Tp.denote p) (sgn a).fst)
          → (h : Prop) × (h → (Tp.denote p (sgn a).snd))}
    (_ : b = @Builtin.newGenericPureBuiltin A sgn desc)
    (args : HList (Tp.denote p) (sgn a).fst) : Prop :=
  STHoare p Γ ⟦⟧
    (.callBuiltin (sgn a).fst (sgn a).snd b args)
    (fun v => ∃∃ h, SLP.lift (α := State p) (v = (desc a args).snd h))

/--
Shorthand for a total Hoare triple about a pure generic *total* builtin
whose description is `fun _ => desc a args`.
-/
abbrev STHoarePureBuiltin' {A : Type} (p : Prime) (Γ : Env)
    {a : A}
    {sgn : A → List Tp × Tp}
    {desc : {p : Prime}
          → (a : A)
          → (args : HList (Tp.denote p) (sgn a).fst)
          → (Tp.denote p (sgn a).snd)}
    (args : HList (Tp.denote p) (sgn a).fst) : Prop :=
  STHoare p Γ ⟦⟧
    (.callBuiltin (sgn a).fst (sgn a).snd
      (@Builtin.newGenericPureBuiltin A sgn
        (@fun _ a args => ⟨True, fun _ => @desc _ a args⟩))
      args)
    (fun v => v = desc a args)

namespace STHoare

private theorem refl_star_top {p : Prime} {α : Type}
    {H : SLP (State p)} {v : α} {st : State p}
    (h : (⟦⟧ ⋆ H) st) :
    ((⟦v = v⟧ ⋆ H) ⋆ ⊤) st :=
  SLP.ent_star_top st
    (SLP.pure_right rfl SLP.entails_self st
      ((@SLP.true_star (State p) _ H) ▸ h))

private theorem post_letIn_ent {p : Prime}
    {X H : SLP (State p)} :
    (X ⋆ (H ⋆ ⊤)) ⋆ ⊤ ⊢ (X ⋆ H) ⋆ ⊤ := by
  kan_intro st
  kan_intro h
  kan_have heq : ((X ⋆ (H ⋆ ⊤)) ⋆ ⊤) = ((X ⋆ H) ⋆ ⊤) := by
    kan_rw [<- @SLP.star_assoc (State p) _ X H ⊤]
    kan_rw [@SLP.star_assoc (State p) _ (X ⋆ H) ⊤ ⊤]
    kan_rw [@SLP.top_star_top (State p) _]
  kan_exact heq ▸ h

private theorem swap_frame_top {p : Prime}
    {X H : SLP (State p)} :
    ((X ⋆ H) ⋆ ⊤) = (H ⋆ (X ⋆ ⊤)) := by
  kan_rw [@SLP.star_comm (State p) _ X H]
  kan_rw [@SLP.star_assoc (State p) _ H X ⊤]

private theorem double_top_collapse {p : Prime} {X : SLP (State p)} :
    (X ⋆ ⊤) ⋆ ⊤ ⊢ X ⋆ ⊤ := by
  kan_intro st
  kan_intro h
  kan_have heq : ((X ⋆ ⊤) ⋆ ⊤ : SLP (State p)) = (X ⋆ ⊤) := by
    kan_rw [@SLP.star_assoc (State p) _ X ⊤ ⊤]
    kan_rw [@SLP.top_star_top (State p) _]
  kan_exact heq ▸ h

theorem frame {p : Prime} {Γ : Env} {tp : Tp} {P H : SLP (State p)}
    {e : Expr (Tp.denote p) tp} {Q : Tp.denote p tp → SLP (State p)}
    (h_hoare : STHoare p Γ P e Q) :
    STHoare p Γ (P ⋆ H) e (fun v => Q v ⋆ H) := by
  kan_intro H'
  kan_exact THoare.consequence
    (H₁ := P ⋆ (H ⋆ H'))
    (Q₁ := fun v => (Q v ⋆ (H ⋆ H')) ⋆ ⊤)
    (fun st h => (SLP.star_assoc (F := P) (G := H) (H := H')) ▸ h)
    (h_hoare (H ⋆ H'))
    (fun v st h =>
      (SLP.star_assoc (F := Q v) (G := H) (H := H')).symm ▸ h)

theorem consequence
    {p : Prime} {Γ : Env} {tp : Tp}
    {e : Expr (Tp.denote p) tp}
    {H₁ H₂ : SLP (State p)}
    {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_pre_conseq : H₂ ⊢ H₁)
    (h_post_conseq : ∀ v, Q₁ v ⋆ ⊤ ⊢ Q₂ v ⋆ ⊤)
    (h_hoare : STHoare p Γ H₁ e Q₁) :
    STHoare p Γ H₂ e Q₂ := by
  kan_intro H
  kan_exact THoare.consequence
    (H₁ := H₁ ⋆ H)
    (Q₁ := fun v => (Q₁ v ⋆ H) ⋆ ⊤)
    (SLP.star_mono_r h_pre_conseq)
    (h_hoare H)
    (fun v st h =>
      have e1 : ((Q₁ v ⋆ H) ⋆ ⊤) = (H ⋆ (Q₁ v ⋆ ⊤)) :=
        swap_frame_top
      have e2 : ((Q₂ v ⋆ H) ⋆ ⊤) = (H ⋆ (Q₂ v ⋆ ⊤)) :=
        swap_frame_top
      e2 ▸ SLP.star_mono_l (h_post_conseq v) st (e1 ▸ h))

theorem ramified_frame_top
    {p : Prime} {Γ : Env} {tp : Tp}
    {e : Expr (Tp.denote p) tp}
    {H₁ H₂ : SLP (State p)}
    {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_hoare : STHoare p Γ H₁ e Q₁)
    (h_ent : H₂ ⊢ H₁ ⋆ (SLP.forall' (fun v => Q₁ v -⋆ (Q₂ v ⋆ ⊤)))) :
    STHoare p Γ H₂ e Q₂ :=
  consequence h_ent
    (fun v =>
      SLP.entails_trans
        (SLP.star_mono_r
          (SLP.star_mono_l
            (SLP.forall_left (a := v) SLP.entails_self)))
        (SLP.entails_trans
          (SLP.star_mono_r SLP.wand_cancel)
          double_top_collapse))
    (frame h_hoare)

theorem consequence_frame
    {p : Prime} {Γ : Env} {tp : Tp}
    {e : Expr (Tp.denote p) tp}
    {H H₁ P : SLP (State p)}
    {Q Q₁ : Tp.denote p tp → SLP (State p)}
    (h_hoare : STHoare p Γ H₁ e Q₁)
    (h_ent : H ⊢ (H₁ ⋆ P))
    (q_ent : ∀ v, Q₁ v ⋆ P ⊢ Q v ⋆ ⊤) :
    STHoare p Γ H e Q :=
  ramified_frame_top h_hoare
    (SLP.entails_trans h_ent
      (SLP.star_mono_l
        (SLP.forall_right (fun v =>
          SLP.wand_intro (fun st h =>
            q_ent v st ((@SLP.star_comm (State p) _ P (Q₁ v)) ▸ h))))))

theorem consequence_frame_left
    {p : Prime} {Γ : Env} {tp : Tp}
    {e : Expr (Tp.denote p) tp}
    {H H₁ H₂ : SLP (State p)}
    {Q : Tp.denote p tp → SLP (State p)}
    (h_hoare : STHoare p Γ H₁ e Q)
    (h_ent : H ⊢ (H₁ ⋆ H₂)) :
    STHoare p Γ H e (fun v => Q v ⋆ H₂) :=
  ramified_frame_top h_hoare
    (SLP.entails_trans h_ent
      (SLP.star_mono_l
        (SLP.forall_right (fun v =>
          SLP.wand_intro (fun st h =>
            SLP.ent_star_top st
              ((@SLP.star_comm (State p) _ H₂ (Q v)) ▸ h))))))

theorem is_mono
    {p : Prime} {Γ₁ Γ₂ : Env} {tp : Tp}
    {pre : SLP (State p)} {expr : Expr (Tp.denote p) tp}
    {post : Tp.denote p tp → SLP (State p)}
    (inner_sub_outer : Γ₁ ⊆ Γ₂) :
    STHoare p Γ₁ pre expr post → STHoare p Γ₂ pre expr post := by
  kan_intro h
  kan_intro H
  kan_intro st
  kan_intro hp
  kan_exact Omni.is_mono inner_sub_outer (h H st hp)

theorem var_intro {p : Prime} {Γ : Env} {tp : Tp} {v : Tp.denote p tp} :
    STHoare p Γ ⟦⟧ (.var v) (fun v' => ⟦v' = v⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.var
  kan_exact refl_star_top h

theorem litU_intro {p : Prime} {Γ : Env} {s : Nat} {n : Int} :
    STHoare p Γ ⟦⟧ (.litNum (.u s) n) (fun v => ⟦v = (n : U s)⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.litU
  kan_exact refl_star_top h

theorem litI_intro {p : Prime} {Γ : Env} {s : Nat} {n : Int} :
    STHoare p Γ ⟦⟧ (.litNum (.i s) n) (fun v => ⟦v = (n : I s)⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.litI
  kan_exact refl_star_top h

theorem litField_intro {p : Prime} {Γ : Env} {n : Int} :
    STHoare p Γ ⟦⟧ (.litNum .field n) (fun v => ⟦v = (n : Fp p)⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.litField
  kan_exact refl_star_top h

theorem litFalse_intro {p : Prime} {Γ : Env} :
    STHoare p Γ ⟦⟧ (.litNum .bool 0) (fun v => ⟦v = false⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.litFalse
  kan_exact refl_star_top h

theorem litTrue_intro {p : Prime} {Γ : Env} :
    STHoare p Γ ⟦⟧ (.litNum .bool 1) (fun v => ⟦v = true⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.litTrue
  kan_exact refl_star_top h

theorem litStr_intro {p : Prime} {Γ : Env}
    {u : U 32} {s : NoirStr u.toNat} :
    STHoare p Γ ⟦⟧ (.litStr u s) (fun v => ⟦v = s⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.litStr
  kan_exact refl_star_top h

theorem fmtStr_intro {p : Prime} {Γ : Env}
    {u : U 32} {tps : Tp} {s : FormatString u tps} :
    STHoare p Γ ⟦⟧ (.fmtStr u tps s) (fun v => ⟦v = s⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.fmtStr
  kan_exact refl_star_top h

theorem letIn_intro {p : Prime} {Γ : Env} {tp₁ tp₂ : Tp}
    {e₁ : Expr (Tp.denote p) tp₁}
    {e₂ : Tp.denote p tp₁ → Expr (Tp.denote p) tp₂}
    {P : SLP (State p)} {Q : Tp.denote p tp₁ → SLP (State p)}
    {R : Tp.denote p tp₂ → SLP (State p)}
    (h_first : STHoare p Γ P e₁ Q)
    (h_rest : ∀ v, STHoare p Γ (Q v) (e₂ v) R) :
    STHoare p Γ P (Expr.letIn e₁ e₂) R := by
  kan_intro H
  kan_exact THoare.letIn_intro
    (P := fun v => (Q v ⋆ H) ⋆ ⊤)
    (h_first H)
    (fun v =>
      THoare.consequence
        (H₁ := Q v ⋆ (H ⋆ ⊤))
        (Q₁ := fun v' => (R v' ⋆ (H ⋆ ⊤)) ⋆ ⊤)
        (fun st h => (@SLP.star_assoc (State p) _ (Q v) H ⊤) ▸ h)
        (h_rest v (H ⋆ ⊤))
        (fun v' => post_letIn_ent (X := R v') (H := H)))

theorem fresh_intro {p : Prime} {Γ : Env} {tp : Tp} :
    STHoare p Γ ⟦⟧ (.callBuiltin [] tp Builtin.fresh h![]) (fun _ => ⟦⟧) := by
  kan_intro H
  kan_exact THoare.consequence
    (H₁ := SLP.forall' (fun _ : Tp.denote p tp => ((⟦⟧ ⋆ H) ⋆ ⊤)))
    (Q₁ := fun _ => ((⟦⟧ ⋆ H) ⋆ ⊤))
    (SLP.forall_right (fun _ => SLP.ent_star_top))
    THoare.fresh_intro
    (fun _ => SLP.entails_self)

theorem iteTrue_intro {p : Prime} {Γ : Env} {tp : Tp}
    {P : SLP (State p)} {Q : Tp.denote p tp → SLP (State p)}
    {mainBody elseBody : Expr (Tp.denote p) tp} :
    STHoare p Γ P mainBody Q →
    STHoare p Γ P (.ite true mainBody elseBody) Q := by
  kan_intro h
  kan_intro H
  kan_intro st
  kan_intro hp
  kan_apply Omni.iteTrue
  kan_exact h H st hp

theorem iteFalse_intro {p : Prime} {Γ : Env} {tp : Tp}
    {P : SLP (State p)} {Q : Tp.denote p tp → SLP (State p)}
    {mainBody elseBody : Expr (Tp.denote p) tp} :
    STHoare p Γ P elseBody Q →
    STHoare p Γ P (.ite false mainBody elseBody) Q := by
  kan_intro h
  kan_intro H
  kan_intro st
  kan_intro hp
  kan_apply Omni.iteFalse
  kan_exact h H st hp

theorem ite_intro {p : Prime} {Γ : Env} {tp : Tp} {cnd : Bool}
    {P : SLP (State p)} {Q : Tp.denote p tp → SLP (State p)}
    {mainBody elseBody : Expr (Tp.denote p) tp}
    (h₁ : cnd = true → STHoare p Γ P mainBody Q)
    (h₂ : cnd = false → STHoare p Γ P elseBody Q) :
    STHoare p Γ P (.ite cnd mainBody elseBody) Q :=
  if h : cnd = true then
    h ▸ iteTrue_intro (h₁ h)
  else
    have hf : cnd = false := Bool.eq_false_iff.mpr h
    hf ▸ iteFalse_intro (h₂ hf)

theorem constU_intro {p : Prime} {Γ : Env} {w : Nat} {c : U w} :
    STHoare p Γ ⟦⟧ (.constU c) (fun v => ⟦v = c⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.constU
  kan_exact refl_star_top h

theorem constFp_intro {p : Prime} {Γ : Env} {c : Int} :
    STHoare p Γ ⟦⟧ (.constFp c) (fun v => ⟦v = (c : Fp p)⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.constFp
  kan_exact refl_star_top h

theorem skip_intro {p : Prime} {Γ : Env} :
    STHoare p Γ ⟦⟧ (.skip) (fun v => ⟦v = ()⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.skip
  kan_exact refl_star_top h

theorem fn_intro {p : Prime} {Γ : Env} {argTps : List Tp} {outTp : Tp}
    {r : FuncRef argTps outTp} :
    STHoare p Γ ⟦⟧ (.fn argTps outTp r) (fun v => ⟦v = r⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.fn
  kan_exact refl_star_top h

theorem litUnit_intro {p : Prime} {Γ : Env} {n : Int} :
    STHoare p Γ ⟦⟧ (.litNum .unit n) (fun v => ⟦v = ()⟧) := by
  kan_intro H
  kan_intro st
  kan_intro h
  kan_apply Omni.litUnit
  kan_exact refl_star_top h

/-- Introduction rule for lambda expressions.  The post-state exhibits a
fresh lambda reference disjoint from the pre-state's heap; the witness
construction requires finmap disjointness lemmas
(`Finmap.singleton_disjoint_of_not_mem`, `Finmap.insert_eq_singleton_union`)
and is left as `sorry` pending a dedicated lambdas-heap lemma layer. -/
theorem lam_intro {p : Prime} {Γ : Env} {argTps : List Tp} {outTp : Tp}
    {lambdaBody : HList (Tp.denote p) argTps → Expr (Tp.denote p) outTp} :
    STHoare p Γ ⟦⟧ (.lam argTps outTp lambdaBody)
      (fun v => [λv ↦ lambdaBody]) := by sorry

/--
Introduction rule for `Expr.call` resolved via a trait.  Given a trait
resolution certificate, a matching `impls` entry, and a Hoare triple for
the instantiated body, one obtains a Hoare triple for the `.call ... fnRef`
expression where `fnRef = .trait ...`.

Left as `sorry` pending the trait-call plumbing that depends on
`Omni.callTrait`.
-/
theorem callTrait_intro
    {p : Prime} {Γ : Env}
    {argTps : List Tp} {outTp : Tp}
    {H : SLP (State p)} {Q : Tp.denote p outTp → SLP (State p)}
    {selfTp : Tp} {traitName : Ident}
    {traitKinds : List Kind}
    {traitGenerics : HList Kind.denote traitKinds}
    {fnName : Ident}
    {kinds : List Kind}
    {generics : HList Kind.denote kinds}
    {args : HList (Tp.denote p) argTps}
    {impls : List (Ident × Function)}
    {func : Function}
    {fnRef : Tp.denote p (.fn argTps outTp)}
    (_href : H ⊢
      ⟦fnRef = (.trait selfTp traitName traitKinds traitGenerics
        fnName kinds generics)⟧ ⋆ (⊤ : SLP (State p)))
    (_h_trait :
      TraitResolution Γ
        ⟨⟨traitName, traitKinds, traitGenerics⟩, selfTp⟩ impls)
    (_h_fn : (fnName, func) ∈ impls)
    (_hkc : func.generics = kinds)
    (_htci : (func.body _ (_hkc ▸ generics) |>.argTps) = argTps)
    (_htco : (func.body _ (_hkc ▸ generics) |>.outTp) = outTp)
    (_h_hoare : STHoare p Γ H
      (_htco ▸ (func.body _ (_hkc ▸ generics)
        |>.body (_htci ▸ args))) Q)
  : STHoare p Γ H (Expr.call argTps outTp fnRef args) Q := by sorry

end STHoare

end KanLampe
