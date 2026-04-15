import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Field

Port of `Lampe.Builtin.Field`.  Field-element builtins: range
constraints, modulus bit/byte representations, radix conversions,
and conversions between field elements and integer types.
-/

namespace KanLampe.Builtin

/-- `(a : Fp p, w : U 32) ↦ ()` with overflow as an exception when
`a ≥ 2 ^ w`.  Noir: `fn __assert_max_bit_size(self, bit_size : u32)`
on `Field`. -/
def applyRangeConstraint := newPureBuiltin
  ⟨[.field, (.u 32)], .unit⟩
  (fun h![a, w] => ⟨a.val < 2 ^ w.toNat,
    fun _ => ()⟩)

/-- `(_ : Fp p) ↦ numBits p : U 64` assuming `log p + 1 < 2 ^ 64`.
Noir: `fn modulus_num_bits() -> u64` on `Field`. -/
def fModNumBits := newPureBuiltin
  ⟨[.field], (.u 64)⟩
  (@fun p h![_] => ⟨numBits p.natVal < 2 ^ 64,
    fun _ => numBits p.natVal⟩)

/-- `(_ : Fp p) ↦ bits(p) : [u1]` (little-endian).  Noir:
`fn modulus_le_bits() -> [u1]` on `Field`. -/
def fModLeBits := newTotalPureBuiltin
  ⟨[.field], (.vector (.u 1))⟩
  (@fun p h![_] => (RadixVec.toDigitsLE' 2 p.natVal).map BitVec.ofFin)

/-- `(_ : Fp p) ↦ bits(p) : [u1]` (big-endian).  Noir:
`fn modulus_be_bits() -> [u1]` on `Field`. -/
def fModBeBits := newTotalPureBuiltin
  ⟨[.field], (.vector (.u 1))⟩
  (@fun p h![_] => (RadixVec.toDigitsBE' 2 p.natVal).map BitVec.ofFin)

/-- `(_ : Fp p) ↦ bytes(p) : [u8]` (little-endian).  Noir:
`fn modulus_le_bytes() -> [u8]` on `Field`. -/
def fModLeBytes := newTotalPureBuiltin
  ⟨[.field], (.vector (.u 8))⟩
  (@fun p h![_] => (RadixVec.toDigitsLE' R256 p.natVal).map BitVec.ofFin)

/-- `(_ : Fp p) ↦ bytes(p) : [u8]` (big-endian).  Noir:
`fn modulus_be_bytes() -> [u8]` on `Field`. -/
def fModBeBytes := newTotalPureBuiltin
  ⟨[.field], (.vector (.u 8))⟩
  (@fun p h![_] => (RadixVec.toDigitsBE' R256 p.natVal).map BitVec.ofFin)

/-- `(f : Fp p) ↦ (f : U s)` via least-significant `s` bits.  Noir:
`fn from_field(a : Field) -> T` for `uint` of bit size `s`. -/
def uFromField := newGenericTotalPureBuiltin
  (fun s => ⟨[.field], (.u s)⟩)
  (fun s h![f] => BitVec.ofNat s f.val)

/-- `(f : Fp p) ↦ (f : I s)` via least-significant `s` bits.  Noir:
`fn from_field(a : Field) -> T` for `int` of bit size `s`. -/
def iFromField := newGenericTotalPureBuiltin
  (fun s => ⟨[.field], (.i s)⟩)
  (fun s h![f] => BitVec.ofNat s f.val)

/-- `(a : U s) ↦ (a : Fp p)` via zero-extension.  Noir:
`fn as_field(self) -> Field` on `uint`. -/
def uAsField := newGenericTotalPureBuiltin
  (fun s => ⟨[.u s], (.field)⟩)
  (fun _ h![a] => a.toNat)

/-- `(a : I s) ↦ (a : Fp p)` via zero-extension of the Nat value.
Noir: `fn as_field(self) -> Field` on `int`. -/
def iAsField := newGenericTotalPureBuiltin
  (fun s => ⟨[.i s], (.field)⟩)
  (fun _ h![a] => a.toNat)

/-- Modulus bit-representation, little-endian. -/
def modulusLeBits : Builtin := newTotalPureBuiltin
  ⟨[], (.vector (.u 1))⟩
  (fun {p} h![] => (RadixVec.toDigitsLE' 2 p.natVal).map BitVec.ofFin)

/-- Modulus bit-representation, big-endian. -/
def modulusBeBits : Builtin := newTotalPureBuiltin
  ⟨[], (.vector (.u 1))⟩
  (fun {p} h![] => (RadixVec.toDigitsBE' 2 p.natVal).map BitVec.ofFin)

/-- Modulus byte-representation, little-endian. -/
def modulusLeBytes : Builtin := newTotalPureBuiltin
  ⟨[], (.vector (.u 8))⟩
  (fun {p} h![] => (RadixVec.toDigitsLE' R256 p.natVal).map BitVec.ofFin)

/-- Modulus byte-representation, big-endian. -/
def modulusBeBytes : Builtin := newTotalPureBuiltin
  ⟨[], (.vector (.u 8))⟩
  (fun {p} h![] => (RadixVec.toDigitsBE' R256 p.natVal).map BitVec.ofFin)

/-- Number of bits in the modulus. -/
def modulusNumBits : Builtin := newTotalPureBuiltin
  ⟨[], (.u 64)⟩
  (fun {p} h![] => numBits p.natVal)

/-- `(f : Fp p) ↦ bits(f)[0 .. s] : [u1 ; s]` (little-endian).
Fails if `f ≥ 2 ^ s`. -/
def toLeBits : Builtin := newGenericBuiltin
  (fun s => ([.field], .array (.u 1) s))
  fun _ h![f] output =>
    f = RadixVec.ofDigitsLE (r := 2) (output.map BitVec.toFin)

/-- `(f : Fp p) ↦ bits(f)[0 .. s] : [u1 ; s]` (big-endian).  Fails
if `f ≥ 2 ^ s`. -/
def toBeBits : Builtin := newGenericBuiltin
  (fun s => ([.field], .array (.u 1) s))
  fun _ h![f] output =>
    f = RadixVec.ofDigitsBE (r := 2) (output.map BitVec.toFin)

/-- `(f : Fp p, r : U 32) ↦ limbs(f, r)[0 .. s] : [u8 ; s]`
(little-endian).  Fails if `r ≤ 1` or `f ≥ r ^ s`. -/
def toLeRadix : Builtin := newGenericBuiltin
  (fun s => ([.field, .u 32], .array (.u 8) s))
  fun _ h![f, r] output =>
    f = RadixVec.ofLimbsLE r.toNat (output.map BitVec.toNat)

/-- `(f : Fp p, r : U 32) ↦ limbs(f, r)[0 .. s] : [u8 ; s]`
(big-endian).  Fails if `r ≤ 1` or `f ≥ r ^ s`. -/
def toBeRadix : Builtin := newGenericBuiltin
  (fun s => ([.field, .u 32], .array (.u 8) s))
  fun _ h![f, r] output =>
    f = RadixVec.ofLimbsBE r.toNat (output.map BitVec.toNat)

end KanLampe.Builtin
