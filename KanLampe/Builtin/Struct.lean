import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Struct

Port of `Lampe.Builtin.Struct`.  Defines `Member tp tps` (a typed de
Bruijn index into a heterogeneous tuple of Noir types),
`indexTpl` / `replaceTuple'` for projection and update, and the tuple
constructor / projector builtins `makeData`, `getMember`, `mkTuple`,
`projectTuple`.
-/

namespace KanLampe.Builtin

inductive Member : Tp → List Tp → Type where
| head {tp : Tp} {tps : List Tp} : Member tp (tp :: tps)
| tail {tp tp' : Tp} {tps : List Tp} : Member tp tps → Member tp (tp' :: tps)

@[reducible]
def indexTpl {p : Prime} {tp : Tp} : {tps : List Tp}
    → Tp.denoteArgs p tps → Member tp tps → Tp.denote p tp
  | _ :: _, (h, _), .head => h
  | _ :: _, (_, rem), .tail m => indexTpl rem m

@[simp]
theorem indexTpl_head {p : Prime} {tp : Tp} {tps : List Tp}
    (a : Tp.denote p tp) (rest : Tp.denoteArgs p tps) :
    indexTpl (p := p) (Prod.mk a rest) Member.head = a := rfl

@[simp]
theorem indexTpl_tail {p : Prime} {tp tp' : Tp} {tps : List Tp}
    (a : Tp.denote p tp') (rest : Tp.denoteArgs p tps) (m : Member tp tps) :
    indexTpl (p := p) (Prod.mk a rest) (Member.tail m) = indexTpl rest m := rfl

@[reducible]
def replaceTuple' {p : Prime} {tp : Tp} : {tps : List Tp}
    → Tp.denoteArgs p tps → Member tp tps → Tp.denote p tp
    → Tp.denoteArgs p tps
  | _ :: _, (_, rem), .head, v => (v, rem)
  | _ :: _, (h, rem), .tail m, v => (h, replaceTuple' rem m v)

@[simp]
theorem replaceTuple'_head {p : Prime} {tp : Tp} {tps : List Tp}
    (a : Tp.denote p tp) (rest : Tp.denoteArgs p tps) (v : Tp.denote p tp) :
    replaceTuple' (p := p) (Prod.mk a rest) Member.head v = (v, rest) := rfl

@[simp]
theorem replaceTuple'_tail {p : Prime} {tp tp' : Tp} {tps : List Tp}
    (a : Tp.denote p tp') (rest : Tp.denoteArgs p tps) (m : Member tp tps)
    (v : Tp.denote p tp) :
    replaceTuple' (p := p) (Prod.mk a rest) (Member.tail m) v
      = (a, replaceTuple' rest m v) := rfl

@[simp]
theorem index_replaced_tpl {p : Prime} {tp : Tp} : {tps : List Tp}
    → (tpl : Tp.denoteArgs p tps) → (mem : Member tp tps)
    → (v' : Tp.denote p tp)
    → indexTpl (replaceTuple' tpl mem v') mem = v'
  | _ :: _, (_, _), .head, _ => rfl
  | _ :: _, (_, rest), .tail m, v' => index_replaced_tpl rest m v'

/-- Builtin tuple constructor (by-name). -/
def makeData := newGenericTotalPureBuiltin
  (fun (x : Option String × List Tp) => ⟨x.2, (.tuple x.1 x.2)⟩)
  (fun {p} (x : Option String × List Tp) fieldExprs => HList.toTuple p fieldExprs x.1)

/-- Projection out of a tuple via a `Member`. -/
def getMember {outTp : Tp} {fieldTps : List Tp}
    (mem : Member outTp fieldTps) := newGenericTotalPureBuiltin
  (fun (name : Option String) => ⟨[.tuple name fieldTps], outTp⟩)
  (fun _ h![tpl] => indexTpl tpl mem)

/-- Alias of `makeData`. -/
def mkTuple := newGenericTotalPureBuiltin
  (fun (x : Option String × List Tp) => ⟨x.2, (.tuple x.1 x.2)⟩)
  (fun {p} (x : Option String × List Tp) fieldExprs => HList.toTuple p fieldExprs x.1)

/-- Alias of `getMember`. -/
def projectTuple {outTp : Tp} {fieldTps : List Tp}
    (mem : Member outTp fieldTps) := newGenericTotalPureBuiltin
  (fun (name : Option String) => ⟨[.tuple name fieldTps], outTp⟩)
  (fun _ h![tpl] => indexTpl tpl mem)

end KanLampe.Builtin
