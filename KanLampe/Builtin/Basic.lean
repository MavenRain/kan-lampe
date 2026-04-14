import KanLampe.SeparationLogic.ValHeap
import KanLampe.Data.Field
import KanLampe.Data.HList
import KanLampe.Data.Digits
import KanLampe.Tp

/-!
# KanLampe.Builtin.Basic

Port of `Lampe.Builtin.Basic`.  Defines the `Builtin` structure, its
`Omni` semantics with `omni_conseq` / `omni_frame` laws, the generic
builders `newGenericBuiltin` / `newGenericPureBuiltin` /
`newPureBuiltin` / `newTotalPureBuiltin`, and the primitive builtins
`assert`, `staticAssert`, `fresh`, and `arrayLen`.
-/

universe u v

namespace KanLampe

abbrev Builtin.Omni := ∀ (P : Prime),
    ValHeap P →
    (argTps : List Tp) →
    (outTp : Tp) →
    HList (Tp.denote P) argTps →
    (Option (ValHeap P × Tp.denote P outTp) → Prop) →
    Prop

def Builtin.omni_conseq (omni : Builtin.Omni) : Prop :=
  ∀ {P st argTps outTp args Q Q'},
    omni P st argTps outTp args Q → (∀ r, Q r → Q' r) →
    omni P st argTps outTp args Q'

def Builtin.omni_frame (omni : Builtin.Omni) : Prop :=
  ∀ {P st₁ st₂ argTps outTp args Q},
    omni P st₁ argTps outTp args Q →
    st₁.Disjoint st₂ →
    omni P (st₁ ∪ st₂) argTps outTp args (fun r => match r with
      | some (st, v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st
      | none => Q none)

structure Builtin where
  omni : Builtin.Omni
  conseq : Builtin.omni_conseq omni
  frame : Builtin.omni_frame omni

end KanLampe

namespace KanLampe.Builtin

inductive genericOmni {A : Type}
    (sgn : A → List Tp × Tp)
    (desc : {p : Prime} → (a : A) → (args : HList (Tp.denote p) (sgn a).fst)
      → (Tp.denote p (sgn a).snd) → Prop)
    : Omni where
  | ok {p st a args Q val} :
      (h : desc a args val) → Q (some (st, val))
      → (genericOmni sgn desc) p st (sgn a).fst (sgn a).snd args Q
  | err {p st a args Q} :
      (h : ∀ val, ¬ desc a args val) → Q none
      → (genericOmni sgn desc) p st (sgn a).fst (sgn a).snd args Q

def newGenericBuiltin {A : Type}
    (sgn : A → List Tp × Tp)
    (desc : {p : Prime} → (a : A) → (args : HList (Tp.denote p) (sgn a).fst)
      → (Tp.denote p (sgn a).snd) → Prop) : Builtin := {
  omni := genericOmni sgn desc
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
      | ok h_desc h_Q => kan_exact genericOmni.ok h_desc (h_imp _ h_Q)
      | err h_neg h_Q => kan_exact genericOmni.err h_neg (h_imp _ h_Q)
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
      | ok h_desc h_Q =>
          kan_exact genericOmni.ok h_desc ⟨st₁, st₂, hdis, rfl, h_Q, rfl⟩
      | err h_neg h_Q => kan_exact genericOmni.err h_neg h_Q
}

inductive genericPureOmni {A : Type}
    (sgn : A → List Tp × Tp)
    (desc : {p : Prime}
      → (a : A)
      → (args : HList (Tp.denote p) (sgn a).fst)
      → (h : Prop) × (h → (Tp.denote p (sgn a).snd)))
    : Omni where
  | ok {p st a args Q} :
      (h : (desc a args).fst)
      → Q (some (st, (desc a args).snd h))
      → (genericPureOmni sgn desc) p st (sgn a).fst (sgn a).snd args Q
  | err {p st a args Q} :
      ¬ ((desc a args).fst) → Q none
      → (genericPureOmni sgn desc) p st (sgn a).fst (sgn a).snd args Q

/--
A generic pure deterministic `Builtin` definition.
Takes a signature `sgn : A → List Tp × Tp`,
where the first element evaluates to a list of input types and the second
element evaluates to the output type.
-/
def newGenericPureBuiltin {A : Type}
    (sgn : A → List Tp × Tp)
    (desc : {p : Prime}
      → (a : A)
      → (args : HList (Tp.denote p) (sgn a).fst)
      → (h : Prop) × (h → (Tp.denote p (sgn a).snd))) : Builtin := {
  omni := genericPureOmni sgn desc
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
      | ok h_desc h_Q => kan_exact genericPureOmni.ok h_desc (h_imp _ h_Q)
      | err h_neg h_Q => kan_exact genericPureOmni.err h_neg (h_imp _ h_Q)
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
      | ok h_desc h_Q =>
          kan_exact genericPureOmni.ok h_desc ⟨st₁, st₂, hdis, rfl, h_Q, rfl⟩
      | err h_neg h_Q => kan_exact genericPureOmni.err h_neg h_Q
}

def newGenericTotalPureBuiltin {A : Type}
    (sgn : A → List Tp × Tp)
    (desc : {p : Prime}
      → (a : A)
      → (args : HList (Tp.denote p) (sgn a).fst)
      → (Tp.denote p (sgn a).snd)) : Builtin :=
  newGenericPureBuiltin sgn (fun a args => ⟨True, fun _ => desc a args⟩)

/--
A pure deterministic `Builtin` definition.
-/
def newPureBuiltin
    (sgn : List Tp × Tp)
    (desc : {p : Prime}
      → (args : HList (Tp.denote p) sgn.fst)
      → (h : Prop) × (h → (Tp.denote p sgn.snd))) :=
  newGenericPureBuiltin
    (fun (_ : Unit) => sgn)
    (fun _ args => desc args)

def newTotalPureBuiltin
    (sgn : List Tp × Tp)
    (desc : {p : Prime}
      → (args : HList (Tp.denote p) sgn.fst)
      → (Tp.denote p sgn.snd)) :=
  newGenericTotalPureBuiltin
    (fun (_ : Unit) => sgn)
    (fun _ args => desc args)

/--
The assertion builtin: takes a boolean.  If `a == true`, it evaluates to `()`,
otherwise an exception is thrown.
-/
def assert := newPureBuiltin
  ⟨[.bool], .unit⟩
  (fun h![a] => ⟨a == true, fun _ => ()⟩)

/--
The static assertion builtin: takes a boolean and a message of type `tp`.
-/
def staticAssert := newGenericPureBuiltin
  (fun tp => ⟨[.bool, tp], .unit⟩)
  (fun _ h![a, _] => ⟨a == true, fun _ => ()⟩)

inductive freshOmni : Omni where
  | mk {P st tp Q} : (∀ v, Q (some (st, v))) → freshOmni P st [] tp h![] Q

/-- Corresponds to an unconstrained function call. -/
def fresh : Builtin := {
  omni := freshOmni
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
      | mk h_all => kan_exact freshOmni.mk (fun v => h_imp _ (h_all v))
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
      | mk h_all =>
          kan_exact freshOmni.mk (fun v => ⟨st₁, st₂, hdis, rfl, h_all v, rfl⟩)
}

inductive ArrayLenCase where
  | vector (tp : Tp)
  | array (tp : Tp) (N : U 32)

def arrayLenSgn : ArrayLenCase → List Tp × Tp
  | .vector tp => ⟨[Tp.vector tp], Tp.u 32⟩
  | .array tp N => ⟨[Tp.array tp N], Tp.u 32⟩

def arrayLenDesc : {p : Prime}
    → (a : ArrayLenCase)
    → (args : HList (Tp.denote p) (arrayLenSgn a).fst)
    → (h : Prop) × (h → Tp.denote p (arrayLenSgn a).snd)
  | _, .vector _, h![x] => ⟨x.length < 2 ^ 32, fun h => BitVec.ofNatLT x.length h⟩
  | _, .array _ N, h![_] => ⟨True, fun _ => N⟩

/--
Evaluates to an array (or vector)'s length `n`.  Evaluates to `U 32`; we
assume `n < 2 ^ 32`.  In Noir, corresponds to `fn len(self) -> u32`
implemented for `[_; n]`.
-/
def arrayLen : Builtin :=
  newGenericPureBuiltin arrayLenSgn arrayLenDesc

end KanLampe.Builtin
