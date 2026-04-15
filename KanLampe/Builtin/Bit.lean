import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Bit

Port of `Lampe.Builtin.Bit`.  Boolean and bitwise builtins over
`Bool`, `U s`, and `I s`.  Purely definitional; no tactic proofs.
-/

namespace KanLampe.Builtin

/-- `(a : Bool) ↦ ¬a : Bool`. -/
def bNot := newTotalPureBuiltin
  ⟨[(.bool)], .bool⟩
  (fun h![a] => a.not)

/-- `(a b : Bool) ↦ a || b : Bool`. -/
def bOr := newTotalPureBuiltin
  ⟨[(.bool), (.bool)], .bool⟩
  (fun h![a, b] => a || b)

/-- `(a b : Bool) ↦ a && b : Bool`. -/
def bAnd := newTotalPureBuiltin
  ⟨[(.bool), (.bool)], .bool⟩
  (fun h![a, b] => a && b)

/-- `(a b : Bool) ↦ a.xor b : Bool`. -/
def bXor := newTotalPureBuiltin
  ⟨[(.bool), (.bool)], .bool⟩
  (fun h![a, b] => a.xor b)

/-- `(a : U s) ↦ ¬a : U s`. -/
def uNot := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s)], (.u s)⟩)
  (fun _ h![a] => a.not)

/-- `(a b : U s) ↦ a ||| b : U s`. -/
def uOr := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => a ||| b)

/-- `(a b : U s) ↦ a &&& b : U s`. -/
def uAnd := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => a &&& b)

/-- `(a b : U s) ↦ a.xor b : U s`. -/
def uXor := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => a.xor b)

/-- `(a b : U s) ↦ a <<< b : U s`. -/
def uShl := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => a <<< b)

/-- `(a b : U s) ↦ a >>> b : U s`. -/
def uShr := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => a >>> b)

/-- `(a : I s) ↦ ¬a : I s`. -/
def iNot := newGenericTotalPureBuiltin
  (fun s => ⟨[(.i s)], (.i s)⟩)
  (fun _ h![a] => a.not)

/-- `(a b : I s) ↦ a ||| b : I s`. -/
def iOr := newGenericTotalPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => a ||| b)

/-- `(a b : I s) ↦ a &&& b : I s`. -/
def iAnd := newGenericTotalPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => a &&& b)

/-- `(a b : I s) ↦ a.xor b : I s`. -/
def iXor := newGenericTotalPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => a.xor b)

/-- `(a b : I s) ↦ a <<< b : I s` with negative shift as an exception. -/
def iShl := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => ⟨b.toInt > 0, fun _ => a <<< b⟩)

/-- `(a b : I s) ↦ a >>> b : I s` with negative shift as an exception. -/
def iShr := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => ⟨b.toInt > 0, fun _ => a >>> b⟩)

end KanLampe.Builtin
