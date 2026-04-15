import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Arith

Port of `Lampe.Builtin.Arith`.  Unsigned / signed integer arithmetic
and field arithmetic builtins.  Each declaration is a call to one
of the generic builtin constructors from `Builtin.Basic`; no tactic
proofs required.
-/

namespace KanLampe.Builtin

/-- `(a b : U s) ↦ a + b : U s` with overflow as an exception. -/
def uAdd := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun s h![a, b] => ⟨(a.toNat + b.toNat) < 2 ^ s,
    fun _ => a + b⟩)

/-- `(a b : U s) ↦ a * b : U s` with overflow as an exception. -/
def uMul := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun s h![a, b] => ⟨(a.toNat * b.toNat) < 2 ^ s,
    fun _ => a * b⟩)

/-- `(a b : U s) ↦ a - b : U s` with underflow as an exception. -/
def uSub := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≤ a,
    fun _ => a - b⟩)

/-- `(a b : U s) ↦ a / b : U s` with division-by-zero as an exception. -/
def uDiv := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a.udiv b⟩)

/-- `(a b : U s) ↦ a % b : U s` with mod-by-zero as an exception. -/
def uRem := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a % b⟩)

/-- `(a b : I s) ↦ a + b : I s` with overflow/underflow as an exception. -/
def iAdd := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt + b.toInt),
    fun _ => a + b⟩)

/-- `(a b : I s) ↦ a - b : I s` with overflow/underflow as an exception. -/
def iSub := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt - b.toInt),
    fun _ => a - b⟩)

/-- `(a b : I s) ↦ a * b : I s` with overflow/underflow as an exception. -/
def iMul := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt * b.toInt),
    fun _ => a * b⟩)

/-- `(a b : I s) ↦ a.sdiv b : I s` with division-by-zero as an exception. -/
def iDiv := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a.sdiv b⟩)

/-- Captures the behaviour of the signed integer remainder operation
`%` in Noir.  For two signed integers `a` and `b` returns
`a - (a.sdiv b) * b`. -/
def intRem {s : Nat} (a b : I s) : I s := a - a.sdiv b * b

example : intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-1)) = 0 := by kan_rfl
example : intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-3)) = -2 := by kan_rfl
example : intRem (BitVec.ofInt 8 (6)) (BitVec.ofInt 8 (-100)) = 6 := by kan_rfl
example : intRem (BitVec.ofInt 8 (127)) (BitVec.ofInt 8 (-3)) = 1 := by kan_rfl

/-- `(a b : I s) ↦ intRem a b : I s` with mod-by-zero as an exception. -/
def iRem := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => intRem a b⟩)

/-- `(a : I s) ↦ -a : I s` with overflow as an exception. -/
def iNeg := newGenericPureBuiltin
  (fun s => ⟨[(.i s)], (.i s)⟩)
  (fun s h![a] => ⟨bitsCanRepresent s (-a.toInt),
    fun _ => -a⟩)

/-- `(a b : Fp p) ↦ a + b : Fp p`. -/
def fAdd := newTotalPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => a + b)

/-- `(a b : Fp p) ↦ a * b : Fp p`. -/
def fMul := newTotalPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => a * b)

/-- `(a b : Fp p) ↦ a - b : Fp p`. -/
def fSub := newTotalPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => a - b)

/-- `(a b : Fp p) ↦ a / b : Fp p` with division-by-zero as an exception. -/
def fDiv := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨b ≠ 0,
    fun _ => a / b⟩)

/-- `(a : Fp p) ↦ -a : Fp p`. -/
def fNeg := newTotalPureBuiltin
  ⟨[(.field)], .field⟩
  (fun h![a] => -a)

/-- `(a b : Fp p) ↦ a != b : Bool`. -/
def fNeq := newTotalPureBuiltin
  ⟨[.field, .field], .bool⟩
  (fun h![a, b] => a != b)

end KanLampe.Builtin
