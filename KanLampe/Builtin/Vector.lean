import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Vector

Port of `Lampe.Builtin.Vector`.  Builtins operating on Noir's
length-indexed vector type `[T]` (called a "slice" in the old Noir
surface syntax).
-/

namespace KanLampe.Builtin

/-- In-place update of a vector at index `i`. -/
@[reducible]
def replaceVector' {p : Prime} {tp : Tp}
    (s : Tp.denote p (.vector tp)) (i : Fin s.length) (v : Tp.denote p tp) :
    Tp.denote p (.vector tp) :=
  List.modify s i (fun _ => v)

@[simp]
theorem replaceVector_length_eq_length {p : Prime} {tp : Tp}
    {s : Tp.denote p (.vector tp)} {i : Fin s.length} {v : Tp.denote p tp} :
    (replaceVector' s i v).length = s.length := by
  kan_simp_all [List.length_modify]

@[simp]
theorem index_replaced_vector {p : Prime} {tp : Tp}
    {s : Tp.denote p (.vector tp)} {idx : Fin s.length} {v : Tp.denote p tp}
    {h : idx.val < (replaceVector' s idx v).length} :
    (replaceVector' s idx v).get ⟨idx.val, h⟩ = v := by
  kan_simp_all [List.modify_eq_set_getElem?, List.getElem_eq_iff]

/-- Builtin vector constructor. -/
def mkVector := newGenericTotalPureBuiltin
  (fun (n, tp) => ⟨List.replicate n tp, (.vector tp)⟩)
  (fun _ args => HList.toList args)

/-- Builtin repeated-vector constructor. -/
def mkRepeatedVector := newGenericTotalPureBuiltin
  (fun (a : Tp) => ⟨[Tp.u 32, a], (.vector a)⟩)
  (fun _ h![n, val] => List.replicate n.toNat val)

/-- `(l : [T], i : U 32) ↦ l[i] : T` with out-of-bounds as an exception. -/
def vectorIndex := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp, .u 32], tp⟩)
  (fun _ h![l, i] => ⟨i.toNat < l.length,
    fun h => l.get (Fin.mk i.toNat h)⟩)

/-- `(l : [T], e : T) ↦ l ++ [e] : [T]`. -/
def vectorPushBack := newGenericTotalPureBuiltin
  (fun tp => ⟨[.vector tp, tp], .vector tp⟩)
  (fun _ h![l, e] => l ++ [e])

/-- `(l : [T], e : T) ↦ [e] ++ l : [T]`. -/
def vectorPushFront := newGenericTotalPureBuiltin
  (fun tp => ⟨[.vector tp, tp], .vector tp⟩)
  (fun _ h![l, e] => [e] ++ l)

/-- `(l : [T], i : U 32, e : T) ↦ l.insertIdx i e : [T]` with out-of-bounds
as an exception. -/
def vectorInsert := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp, .u 32, tp], .vector tp⟩)
  (fun _ h![l, i, e] => ⟨i.toNat < l.length,
    fun _ => l.insertIdx i.toNat e⟩)

/-- `(l : [T]) ↦ (l.head, l.tail) : (T, [T])`.  Empty vectors throw. -/
def vectorPopFront := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp], .tuple none [tp, .vector tp]⟩)
  (fun _ h![l] => ⟨l ≠ [],
    fun h => (l.head h, l.tail, ())⟩)

/-- `(l : [T]) ↦ (l.dropLast, l.getLast) : ([T], T)`.  Empty vectors throw. -/
def vectorPopBack := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp], .tuple none [.vector tp, tp]⟩)
  (fun _ h![l] => ⟨l ≠ [],
    fun h => (l.dropLast, l.getLast h, ())⟩)

/-- `(l : [T], i : U 32) ↦ (l \ l[i], l[i]) : ([T], T)` with out-of-bounds
as an exception. -/
def vectorRemove := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp, .u 32], .tuple none [.vector tp, tp]⟩)
  (fun _ h![l, i] => ⟨i.toNat < l.length,
    fun h => (l.eraseIdx i.toNat, l.get (Fin.mk i.toNat h), ())⟩)

end KanLampe.Builtin
