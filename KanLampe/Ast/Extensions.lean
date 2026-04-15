import KanLampe.Ast
import KanLampe.Builtin

/-!
# KanLampe.Ast.Extensions

Port of `Lampe.Ast.Extensions`.  Convenience wrappers around
`Expr.callBuiltin` for reference, vector, array, tuple, and lens
operations.
-/

namespace KanLampe

/-- Reference allocation. -/
@[reducible]
def Expr.ref {rep : Tp → Type} {tp : Tp} (val : rep tp) : Expr rep tp.ref :=
  Expr.callBuiltin [tp] tp.ref .ref h![val]

/-- Reference read. -/
@[reducible]
def Expr.readRef {rep : Tp → Type} {tp : Tp} (ref : rep tp.ref) : Expr rep tp :=
  Expr.callBuiltin [tp.ref] tp .readRef h![ref]

/-- Reference write. -/
@[reducible]
def Expr.writeRef {rep : Tp → Type} {tp : Tp}
    (ref : rep tp.ref) (val : rep tp) : Expr rep .unit :=
  Expr.callBuiltin [tp.ref, tp] .unit .writeRef h![ref, val]

/-- Vector literal. -/
@[reducible]
def Expr.mkVector {rep : Tp → Type} {tp : Tp}
    (n : Nat) (vals : HList rep (List.replicate n tp)) :
    Expr rep (.vector tp) :=
  Expr.callBuiltin (List.replicate n tp) (.vector tp) .mkVector vals

/-- Array literal. -/
@[reducible]
def Expr.mkArray {rep : Tp → Type} {tp : Tp}
    (n : U 32) (vals : HList rep (List.replicate n.toNat tp)) :
    Expr rep (.array tp n) :=
  Expr.callBuiltin (List.replicate n.toNat tp) (.array tp n) .mkArray vals

/-- Replicated vector literal. -/
@[reducible]
def Expr.mkRepVector {rep : Tp → Type} {tp : Tp}
    (n : Nat) (val : rep tp) : Expr rep (.vector tp) :=
  Expr.callBuiltin (List.replicate n tp) (.vector tp) .mkVector
    (HList.replicate val n)

/-- Replicated array literal. -/
@[reducible]
def Expr.mkRepArray {rep : Tp → Type} {tp : Tp}
    (n : U 32) (val : rep tp) : Expr rep (.array tp n) :=
  Expr.callBuiltin (List.replicate n.toNat tp) (.array tp n) .mkArray
    (HList.replicate val n.toNat)

/-- Tuple literal. -/
@[reducible]
def Expr.mkTuple {rep : Tp → Type} {tps : List Tp}
    (name : Option String) (args : HList rep tps) :
    Expr rep (.tuple name tps) :=
  Expr.callBuiltin tps (.tuple name tps) .mkTuple args

/-- Lens modification. -/
@[reducible]
def Expr.modifyLens {rep : Tp → Type} {tp₁ tp₂ : Tp}
    (r : rep (.ref tp₁)) (v : rep tp₂) (lens : Lens rep tp₁ tp₂) :
    Expr rep .unit :=
  Expr.callBuiltin [.ref tp₁, tp₂] .unit (.modifyLens lens) h![r, v]

/-- Lens read. -/
@[reducible]
def Expr.getLens {rep : Tp → Type} {tp₁ tp₂ : Tp}
    (v : rep tp₁) (lens : Lens rep tp₁ tp₂) : Expr rep tp₂ :=
  Expr.callBuiltin [tp₁] tp₂ (.getLens lens) h![v]

/-- Tuple projection via `Member`. -/
@[reducible]
def Expr.getMember {rep : Tp → Type} {tp : Tp} {name : Option String}
    {tps : List Tp}
    (v : rep (Tp.tuple name tps)) (member : Builtin.Member tp tps) :
    Expr rep tp :=
  Expr.callBuiltin [.tuple name tps] tp (Builtin.getMember member) h![v]

end KanLampe
