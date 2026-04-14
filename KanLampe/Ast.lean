import KanLampe.Tp
import KanLampe.Data.HList
import KanLampe.SeparationLogic.ValHeap
import KanLampe.Builtin.Basic

/-!
# KanLampe.Ast

Port of `Lampe.Ast`.  Defines the core AST: `Expr`, `Lambda`,
`Function`, `FunctionDecl`, `Struct`, `TraitRef`, `TraitImplRef`,
and `TraitImpl`.  Mirrors the upstream structure one-for-one; no
tactic proofs beyond an inhabitation example.
-/

namespace KanLampe

abbrev Ident := String

structure TraitRef where
  name : Ident
  traitGenericKinds : List Kind
  traitGenerics : HList Kind.denote traitGenericKinds

structure TraitImplRef where
  trait : TraitRef
  self : Tp

inductive Expr (rep : Tp → Type) : Tp → Type where
| litNum : (tp : Tp) → Int → Expr rep tp
| litStr : (len : U 32) → NoirStr len.toNat → Expr rep (.str len)
| constFp : Int → Expr rep .field
| constU {w : Nat} : U w → Expr rep (.u w)
| fmtStr : (len : U 32) → (tps : Tp) → FormatString len tps → Expr rep (.fmtStr len tps)
| fn : (argTps : List Tp) → (outTp : Tp) → (r : FuncRef argTps outTp) → Expr rep (.fn argTps outTp)
| var {tp : Tp} : rep tp → Expr rep tp
| letIn {t₁ t₂ : Tp} : Expr rep t₁ → (rep t₁ → Expr rep t₂) → Expr rep t₂
| call : (argTps : List Tp) → (outTp : Tp) → (rep <| .fn argTps outTp) → (args : HList rep argTps) → Expr rep outTp
| callBuiltin : (argTps : List Tp) → (outTp : Tp) → (b : Builtin) → (args : HList rep argTps) → Expr rep outTp
| ite {a : Tp} : rep .bool → Expr rep a → Expr rep a → Expr rep a
| skip : Expr rep .unit
| loop {s : Nat} {r : Tp} : rep (.u s) → rep (.u s) → (rep (.u s) → Expr rep r) → Expr rep .unit
| lam : (argTps : List Tp) → (outTp : Tp) → (HList rep argTps → Expr rep outTp) → Expr rep (.fn argTps outTp)

attribute [pp_nodot] Expr.letIn

structure Lambda (rep : Tp → Type) where
  argTps : List Tp
  outTp : Tp
  body : HList rep argTps → Expr rep outTp

structure Function : Type _ where
  generics : List Kind
  body : ∀ (rep : Tp → Type), (HList Kind.denote generics) → Lambda rep

/-- Polymorphic identity. -/
example : Function := {
  generics := [.type]
  body := fun _ h![tp] => ⟨[tp], tp, fun h![x] => .var x⟩
}

structure FunctionDecl where
  name : Ident
  fn : Function

@[reducible, simp]
def FunctionDecl.call {lp} (f : FunctionDecl)
    (gs : HList Kind.denote f.fn.generics)
    (args : HList (Tp.denote lp) (f.fn.body (Tp.denote lp) gs).argTps) :
    Expr (Tp.denote lp) (f.fn.body (Tp.denote lp) gs).outTp :=
  .call
      (f.fn.body (Tp.denote lp) gs).argTps
      (f.fn.body (Tp.denote lp) gs).outTp
      (FuncRef.decl f.name f.fn.generics gs)
      args

structure Struct where
  name : String
  genericKinds : List Kind
  fieldTypes : HList Kind.denote genericKinds → List Tp

structure TraitImpl where
  traitGenericKinds : List Kind
  implGenericKinds : List Kind
  traitGenerics : HList Kind.denote implGenericKinds → HList Kind.denote traitGenericKinds
  constraints : HList Kind.denote implGenericKinds → List TraitImplRef
  self : HList Kind.denote implGenericKinds → Tp
  impl : HList Kind.denote implGenericKinds → List (Ident × Function)

@[reducible]
def Struct.tp (s : Struct) : HList Kind.denote s.genericKinds → Tp :=
  fun generics => .tuple (some s.name) <| s.fieldTypes generics

end KanLampe
