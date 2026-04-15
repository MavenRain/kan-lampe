import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Array

Port of `Lampe.Builtin.Array`.  Builtins operating on Noir's
length-indexed array type `[T ; n]`, plus the auxiliary
`replaceArray'` update function used by the lens builtins.
-/

namespace KanLampe.Builtin

/-- In-place update of an array at index `idx`. -/
@[reducible]
def replaceArray' {p : Prime} {tp : Tp} {n : U 32}
    (arr : Tp.denote p (.array tp n)) (idx : Fin n.toNat) (v : Tp.denote p tp) :
    Tp.denote p (.array tp n) :=
  let arr' := arr.insertIdx v ⟨idx.val + 1, Nat.succ_lt_succ idx.isLt⟩
  arr'.eraseIdx ⟨idx.val, Nat.lt_succ_of_lt idx.isLt⟩

/-- Builtin array constructor. -/
def mkArray := newGenericTotalPureBuiltin
  (fun (a : U 32 × Tp) => ⟨List.replicate a.1.toNat a.2, (.array a.2 a.1)⟩)
  (fun _ args => HList.toVec args)

/-- Builtin repeated-array constructor. -/
def mkRepeatedArray := newGenericTotalPureBuiltin
  (fun (x : U 32 × Tp) => ⟨[x.2], (.array x.2 x.1)⟩)
  (fun (x : U 32 × Tp) h![val] => List.Vector.replicate x.1.toNat val)

/-- `(l : [T ; n], i : U 32) ↦ l[i] : T` with out-of-bounds as an exception. -/
def arrayIndex := newGenericPureBuiltin
  (fun (x : Tp × U 32) => ⟨[.array x.1 x.2, .u 32], x.1⟩)
  (fun (x : Tp × U 32) h![l, i] => ⟨i.toNat < x.2.toNat,
    fun h => l.get (Fin.mk i.toNat h)⟩)

/-- `(a : [T ; n]) ↦ (a : [T])`.  Noir:
`fn as_vector(self) -> [T]` on `[T ; n]`. -/
def asVector := newGenericTotalPureBuiltin
  (fun (x : Tp × U 32) => ⟨[.array x.1 x.2], .vector x.1⟩)
  (fun _ h![a] => a.toList)

end KanLampe.Builtin
