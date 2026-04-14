import Lean
import KanLampe.Data.Integers
import KanLampe.Data.Field
import KanLampe.Data.HList
import KanLampe.Data.Strings
import KanLampe.Data.Meta

-- Note: This option needs to be defined outside of any namespace for it to register correctly
register_option KanLampe.pp.Tp : Bool := {
  defValue := true
  descr := "Pretty print applications of `Tp.denote`"
}

namespace KanLampe

structure Ref where
  val : Nat
deriving DecidableEq

variable (p : Prime)

inductive Tp where
| u (size : Nat)
| i (size : Nat)
| bool
| unit
| str (size : U 32)
| fmtStr (size : U 32) (argTps : Tp)
| field
| vector (element : Tp)
| array (element : Tp) (size : U 32)
| tuple (name : Option String) (fields : List Tp)
| ref (tp : Tp)
| fn (argTps : List Tp) (outTp : Tp)
deriving BEq

inductive Kind where
| u (size : Nat)
| field
| type
deriving BEq, Nonempty

mutual

def tpsDecEq (a b : List Tp) : Decidable (a = b) := match a, b with
| [], [] => isTrue rfl
| [], _ :: _ => isFalse (fun h => by kan_cases h)
| _ :: _, [] => isFalse (fun h => by kan_cases h)
| tp₁ :: tps₁, tp₂ :: tps₂ => match tpDecEq tp₁ tp₂, tpsDecEq tps₁ tps₂ with
  | isTrue _, isTrue _ =>
    isTrue (by kan_subst_vars; kan_rfl)
  | isTrue _, isFalse h =>
    isFalse (fun heq => h (by kan_cases heq; kan_rfl))
  | isFalse h, isTrue _ =>
    isFalse (fun heq => h (by kan_cases heq; kan_rfl))
  | isFalse h, isFalse _ =>
    isFalse (fun heq => h (by kan_cases heq; kan_rfl))

def tpDecEq (a b : Tp) : Decidable (a = b) := by
  kan_cases a <;> kan_cases b
  case bool.bool => kan_exact isTrue rfl
  case unit.unit => kan_exact isTrue rfl
  case field.field => kan_exact isTrue rfl
  case u.u n₁ n₂ =>
    kan_exact (match decEq n₁ n₂ with
      | isTrue h => isTrue (by kan_subst_vars; kan_rfl)
      | isFalse h => isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  case i.i n₁ n₂ =>
    kan_exact (match decEq n₁ n₂ with
      | isTrue h => isTrue (by kan_subst_vars; kan_rfl)
      | isFalse h => isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  case str.str n₁ n₂ =>
    kan_exact (match decEq n₁ n₂ with
      | isTrue h => isTrue (by kan_subst_vars; kan_rfl)
      | isFalse h => isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  case ref.ref tp₁ tp₂ =>
    kan_exact (match tpDecEq tp₁ tp₂ with
      | isTrue h => isTrue (by kan_subst_vars; kan_rfl)
      | isFalse h => isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  case vector.vector tp₁ tp₂ =>
    kan_exact (match tpDecEq tp₁ tp₂ with
      | isTrue h => isTrue (by kan_subst_vars; kan_rfl)
      | isFalse h => isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  case array.array tp₁ n₁ tp₂ n₂ =>
    kan_exact (match tpDecEq tp₁ tp₂, decEq n₁ n₂ with
      | isTrue _, isTrue _ =>
        isTrue (by kan_subst_vars; kan_rfl)
      | isTrue _, isFalse h =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl))
      | isFalse h, isTrue _ =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl))
      | isFalse h, isFalse _ =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  case fmtStr.fmtStr n₁ tps₁ n₂ tps₂ =>
    kan_exact (match tpDecEq tps₁ tps₂, decEq n₁ n₂ with
      | isTrue _, isTrue _ =>
        isTrue (by kan_subst_vars; kan_rfl)
      | isTrue _, isFalse h =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl))
      | isFalse h, isTrue _ =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl))
      | isFalse h, isFalse _ =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  case tuple.tuple name₁ fs₁ name₂ fs₂ =>
    kan_exact (match tpsDecEq fs₁ fs₂, decEq name₁ name₂ with
      | isTrue _, isTrue _ =>
        isTrue (by kan_subst_vars; kan_rfl)
      | isTrue _, isFalse h =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl))
      | isFalse h, isTrue _ =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl))
      | isFalse h, isFalse _ =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  case fn.fn args₁ out₁ args₂ out₂ =>
    kan_exact (match tpDecEq out₁ out₂, tpsDecEq args₁ args₂ with
      | isTrue _, isTrue _ =>
        isTrue (by kan_subst_vars; kan_rfl)
      | isTrue _, isFalse h =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl))
      | isFalse h, isTrue _ =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl))
      | isFalse h, isFalse _ =>
        isFalse (fun heq => h (by kan_cases heq; kan_rfl)))
  all_goals
    kan_apply Decidable.isFalse
    kan_intro h
    kan_cases h

end

instance : DecidableEq Tp := tpDecEq

instance : DecidableEq <| List Tp := tpsDecEq

@[reducible]
def Kind.denote : Kind → Type
| .u w => U w
| .field => Int
| .type => Tp

def kindDecEq (a b : Kind) : Decidable (a = b) := match a, b with
| .u n₁, .u n₂ => match decEq n₁ n₂ with
  | isTrue h => isTrue (by kan_subst_vars; kan_rfl)
  | isFalse h => isFalse (fun heq => h (by kan_cases heq; kan_rfl))
| .u _, .field => isFalse (fun h => by kan_cases h)
| .u _, .type => isFalse (fun h => by kan_cases h)
| .field, .u _ => isFalse (fun h => by kan_cases h)
| .field, .field => isTrue rfl
| .field, .type => isFalse (fun h => by kan_cases h)
| .type, .u _ => isFalse (fun h => by kan_cases h)
| .type, .field => isFalse (fun h => by kan_cases h)
| .type, .type => isTrue rfl

def kindsDecEq (a b : List Kind) : Decidable (a = b) := match a, b with
| [], [] => isTrue rfl
| [], _ :: _ => isFalse (fun h => by kan_cases h)
| _ :: _, [] => isFalse (fun h => by kan_cases h)
| a :: as, b :: bs => match kindDecEq a b, kindsDecEq as bs with
  | isTrue _, isTrue _ =>
    isTrue (by kan_subst_vars; kan_rfl)
  | isTrue _, isFalse h =>
    isFalse (fun heq => h (by kan_cases heq; kan_rfl))
  | isFalse h, isTrue _ =>
    isFalse (fun heq => h (by kan_cases heq; kan_rfl))
  | isFalse h, isFalse _ =>
    isFalse (fun heq => h (by kan_cases heq; kan_rfl))

instance : DecidableEq Kind := kindDecEq

instance : DecidableEq <| List Kind := kindsDecEq

inductive FuncRef (argTps : List Tp) (outTp : Tp) where
| lambda (r : Ref)
| decl (fnName : String) (kinds : List Kind) (generics : HList Kind.denote kinds)
| trait (selfTp : Tp)
  (traitName : String) (traitKinds : List Kind) (traitGenerics : HList Kind.denote traitKinds)
  (fnName : String) (fnKinds : List Kind) (fnGenerics : HList Kind.denote fnKinds)

def FuncRef.isLambda {a : List Tp} {o : Tp} : FuncRef a o → Bool
| FuncRef.lambda _ => true
| FuncRef.decl _ _ _ => false
| FuncRef.trait _ _ _ _ _ _ _ => false

def FuncRef.asLambda {a : List Tp} {o : Tp} (f : FuncRef a o) (h : FuncRef.isLambda f) : Ref :=
  match h' : f with
  | FuncRef.lambda r => r
  | FuncRef.decl _ _ _ => by kan_cases h
  | FuncRef.trait _ _ _ _ _ _ _ => by kan_cases h

/-- TODO: Actually implement this at some point -/
def FormatString (_len : U 32) (_argTps : Tp) := String

mutual

@[reducible]
def Tp.denoteArgs : List Tp → Type
| [] => Unit
| tp :: tps => denote tp × denoteArgs tps

@[reducible]
def Tp.denote : Tp → Type
| .u n => U n
| .i n => I n
| .bool => Bool
| .unit => Unit
| .str n => NoirStr n.toNat
| .fmtStr n tps => FormatString n tps
| .field => Fp p
| .vector tp => List (denote tp)
| .array tp n => List.Vector (denote tp) n.toNat
| .ref _ => Ref
| .tuple _ fields => Tp.denoteArgs fields
| .fn argTps outTp => FuncRef argTps outTp

end

section Delab

open Lean PrettyPrinter Delaborator SubExpr
open Meta (mkAppM)

abbrev whenDelabTp {α : Type} : DelabM α → DelabM α := whenDelabOptionSet `KanLampe.pp.Tp

/-- convert `[A, B, C, ...]` to the product `A.denote × B.denote × C.denote × ... -/
def delabDenoteArgsAux (p : Expr) (tps : List Expr) : MetaM Expr := do
  let rec loop (acc : Expr) : List Expr → MetaM Expr
  | [] => return acc
  | tp :: tps => do
    let tp ← mkAppM `KanLampe.Tp.denote #[p, tp]
    loop (← mkAppM `Prod #[tp, acc]) tps
  let base ← mkAppM `Unit #[]
  loop base tps

/-- Delaborate `Tp.denote` to its defeq concrete Lean type. This improves the readability of goal
states involving `Tp.denote` -/
@[app_delab KanLampe.Tp.denote]
def delabTpDenote : Delab := whenDelabTp getExpr >>= fun expr => whenFullyApplied expr do
  let_expr Tp.denote p tpExpr := expr | failure
  let tpExpr ← match_expr tpExpr with
  | Tp.field => mkAppM `KanLampe.Fp #[p]
  | Tp.u n => mkAppM `KanLampe.U #[n]
  | Tp.i n => mkAppM `KanLampe.I #[n]
  | Tp.bool => mkAppM `Bool #[]
  | Tp.unit => mkAppM `Unit #[]
  | Tp.str n =>
    let len ← mkAppM `BitVec.toNat #[n]
    mkAppM `KanLampe.NoirStr #[len]
  | Tp.fmtStr n tps => mkAppM `KanLampe.FormatString #[n, tps]
  | Tp.vector tp => mkAppM `List #[← mkAppM `KanLampe.Tp.denote #[p, tp]]
  | Tp.array tp n =>
    let len ← mkAppM `BitVec.toNat #[n]
    mkAppM `List.Vector #[← mkAppM `KanLampe.Tp.denote #[p, tp], len]
  | Tp.ref _ => mkAppM `KanLampe.Ref #[]
  | Tp.tuple _ fields =>
    let (_, tps) ← liftOption fields.listLit?
    delabDenoteArgsAux p tps
  | Tp.fn argTps outTp =>
    mkAppM `KanLampe.FuncRef #[argTps, outTp]
  | _ => failure
  return ← delab tpExpr

end Delab

@[reducible]
def HList.toTuple {tps : List Tp} (hList : HList (Tp.denote p) tps) (name : Option String) :
    Tp.denote p <| .tuple name tps := match hList with
| .nil => ()
| .cons arg args => ⟨arg, HList.toTuple args name⟩

mutual

def Tp.zeroArgs (args : List Tp) : HList (Tp.denote p) args :=
  match args with
  | [] => h![]
  | a :: b => .cons a.zero (Tp.zeroArgs b)

def Tp.zero (tp : Tp) : Tp.denote p tp :=
match tp with
| .u _ | .i _ | .field => 0
| .bool => False
| .unit => ()
| .str n => List.Vector.replicate n.toNat 0
| .fmtStr _ _ => ""
| .vector _ => []
| .array tp n => List.Vector.replicate n.toNat tp.zero
| .ref _ => ⟨0⟩
| .tuple name fields => HList.toTuple p (Tp.zeroArgs fields) name
| .fn _ _ => .lambda ⟨0⟩

end

/- In this section we provide unification hints to assist with the ergonomics of stating theorems -/
section unificationHints

/-- This is slightly dangerous, as it could conflict with the unification with `Tp.i n` -/
unif_hint (p : Prime) (n : Nat) (tp : Tp) where
  Tp.u n =?= tp
  ⊢ Tp.denote p tp =?= BitVec n

unif_hint (p : Prime) (tp : Tp) where
  Tp.bool =?= tp
  ⊢ Tp.denote p tp =?= Bool

unif_hint (p q : Prime) (tp : Tp) where
  p =?= q
  Tp.field =?= tp
  ⊢ Tp.denote p tp =?= Fin (q.val + 1)

unif_hint (p : Prime) (tp tp' : Tp) where
  Tp.vector tp' =?= tp
  ⊢ Tp.denote p tp =?= List (Tp.denote p tp')

unif_hint (n : U 32) (p : Prime) (tp tp' : Tp) where
  Tp.array tp' n =?= tp
  ⊢ Tp.denote p tp =?= List.Vector (Tp.denote p tp') (n.toNat)

elab "tuple_unif_hints" : command => do
  for maxNum in [0:5] do
    let tpHole := Lean.mkIdent `tp

    let tpIdents := List.range maxNum |>.map (fun n => Lean.mkIdent <| .mkSimple s!"tp{n}")
    let tpBinder ← `(bracketedBinder|($(tpIdents.toArray)* : Tp))

    let listType ← `([$(tpIdents.toArray),*])
    let productType ← tpIdents.foldlM (init := ← `(Unit)) fun acc tpIdent => do
      `((Tp.denote p $tpIdent) × $acc)

    let tupleHint ← `(
    unif_hint (p : Prime) (name? : Option String) ($tpHole : Tp) $tpBinder where
      Tp.tuple name? $listType =?= $tpHole
      ⊢ Tp.denote p $tpHole =?= $productType
    )

    Lean.Elab.Command.elabCommand tupleHint

tuple_unif_hints

end unificationHints

-- Deprecated alias for backward compatibility
@[deprecated Tp.vector (since := "2025-03-19")]
abbrev Tp.slice := Tp.vector

end KanLampe
