import KanLampe.Ast
import KanLampe.Builtin.Array
import KanLampe.Builtin.Struct
import KanLampe.Builtin.Vector

/-!
# KanLampe.Lens

Port of `Lampe.Lens`.  Defines `Access rep tp₁ tp₂` (single-step
projection into a tuple, array, or vector) and `Lens rep tp₁ tp₂`
(sequence of accesses), plus their `get` and `modify` operations.
-/

namespace KanLampe

/-- One step of lens projection into an aggregate Noir type. -/
inductive Access (rep : Tp → Type) : Tp → Tp → Type
| tuple  {tp : Tp} {tps : List Tp} {name : Option String} :
    (mem : Builtin.Member tp tps) → Access rep (.tuple name tps) tp
| array  {tp : Tp} {n : U 32} :
    (idx : rep (.u 32)) → Access rep (.array tp n) tp
| vector {tp : Tp} :
    (idx : rep (.u 32)) → Access rep (.vector tp) tp

@[simp]
def Access.get {p : Prime} {tp₁ tp₂ : Tp}
    (acc : Access (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁) :
    Option (Tp.denote p tp₂) :=
  match acc with
  | .tuple mem => Builtin.indexTpl s mem
  | .array (n := n) idx =>
      if h : idx.toNat < n.toNat then s.get ⟨idx.toNat, h⟩ else none
  | .vector idx =>
      if h : idx.toNat < s.length then s.get ⟨idx.toNat, h⟩ else none

@[simp]
def Access.modify {p : Prime} {tp₁ tp₂ : Tp}
    (acc : Access (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁)
    (v' : Tp.denote p tp₂) : Option (Tp.denote p tp₁) :=
  match acc with
  | .tuple mem => Builtin.replaceTuple' s mem v'
  | .array (n := n) idx =>
      if h : idx.toNat < n.toNat then s.set ⟨idx.toNat, h⟩ v' else none
  | .vector idx =>
      if h : idx.toNat < s.length then
        Builtin.replaceVector' s ⟨idx.toNat, h⟩ v'
      else none

/-- A lens between Noir types: a concatenation of `Access` steps. -/
inductive Lens (rep : Tp → Type) : Tp → Tp → Type
| nil {tp : Tp} : Lens rep tp tp
| cons {tp₁ tp₂ tp₃ : Tp} :
    Lens rep tp₁ tp₂ → Access rep tp₂ tp₃ → Lens rep tp₁ tp₃

@[simp]
def Lens.get {p : Prime} {tp₁ tp₂ : Tp}
    (lens : Lens (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁) :
    Option (Tp.denote p tp₂) :=
  match lens with
  | .nil => s
  | .cons l₁ a₁ => (l₁.get s) >>= a₁.get

@[simp]
def Lens.modify {p : Prime} {tp₁ tp₂ : Tp}
    (lens : Lens (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁)
    (v' : Tp.denote p tp₂) : Option (Tp.denote p tp₁) :=
  match lens with
  | .nil => v'
  | .cons l₁ a₂ => (l₁.get s) >>= (a₂.modify · v') >>= l₁.modify s

end KanLampe
