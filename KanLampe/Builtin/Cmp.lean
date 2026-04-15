import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Cmp

Port of `Lampe.Builtin.Cmp`.  Equality, less-than, less-or-equal,
greater-than, and greater-or-equal builtins across the primitive
Noir types.  Purely definitional.
-/

namespace KanLampe.Builtin

/-- `(_ _ : Unit) ↦ true : Bool`. -/
def unitEq := newTotalPureBuiltin
  ⟨[.unit, .unit], .bool⟩
  (fun _ => true)

/-- `(a b : Bool) ↦ a = b : Bool`. -/
def bEq := newTotalPureBuiltin
  ⟨[.bool, .bool], .bool⟩
  (fun h![a, b] => a = b)

/-- `(a b : Fp p) ↦ a = b : Bool`. -/
def fEq := newTotalPureBuiltin
  ⟨[.field, .field], .bool⟩
  (fun h![a, b] => a = b)

/-- `(a b : U s) ↦ a = b : Bool`. -/
def uEq := newGenericTotalPureBuiltin
  (fun s => ⟨[.u s, .u s], .bool⟩)
  (fun _ h![a, b] => a = b)

/-- `(a b : I s) ↦ a = b : Bool`. -/
def iEq := newGenericTotalPureBuiltin
  (fun s => ⟨[.i s, .i s], .bool⟩)
  (fun _ h![a, b] => a = b)

/-- `(a b : str n) ↦ a = b : Bool`. -/
def strEq := newGenericTotalPureBuiltin
  (fun n => ⟨[.str n, .str n], .bool⟩)
  (fun _ h![a, b] => a = b)

/-- `(a b : U s) ↦ a < b : Bool`. -/
def uLt := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => a < b)

/-- `(a b : U s) ↦ a ≤ b : Bool`. -/
def uLeq := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => a ≤ b)

/-- `(a b : U s) ↦ a ≥ b : Bool`. -/
def uGeq := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => a ≥ b)

/-- `(a b : I s) ↦ a < b : Bool`. -/
def iLt := newGenericTotalPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], .bool⟩)
  (fun _ h![a, b] => a < b)

/-- `(a b : U s) ↦ a > b : Bool`. -/
def uGt := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => a > b)

/-- `(a b : I s) ↦ a > b : Bool`. -/
def iGt := newGenericTotalPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], .bool⟩)
  (fun _ h![a, b] => a > b)

/-- `(a b : I s) ↦ a ≠ b : Bool`. -/
def iNeq := newGenericTotalPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], .bool⟩)
  (fun _ h![a, b] => a ≠ b)

/-- `(a b : U s) ↦ a ≠ b : Bool`. -/
def uNeq := newGenericTotalPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => a ≠ b)

end KanLampe.Builtin
