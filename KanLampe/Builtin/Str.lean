import KanLampe.Builtin.Basic
import KanLampe.Data.Strings

/-!
# KanLampe.Builtin.Str

Port of `Lampe.Builtin.Str`.  String/byte-array conversion builtins.
-/

namespace KanLampe.Builtin

/-- `(s : str n) ↦ bytes(s) : [u8 ; n]`.  Noir: `fn as_bytes<let N : u32>(self : str<N>) -> [u8 ; N]`. -/
def strAsBytes := newGenericPureBuiltin
  (fun n => ⟨[.str n], (.array (.u 8) n)⟩)
  (fun n h![s] => ⟨s.length = n.toNat,
    fun _ => s.bytes⟩)

/-- Unchecked conversion of a byte array to a `NoirStr`.  Performs no
validation, matching `arrayAsStrUnchecked` in Noir. -/
def arrayAsStr! {N : Nat} (array : List.Vector (BitVec 8) N) : NoirStr N :=
  let bytes := array.map (fun x => UInt8.ofBitVec x)
  NoirStr.mk bytes

/-- `(a : [u8 ; n]) ↦ (a : str n)`.  Noir:
`fn from<let N : u32>(bytes : [u8, N]) -> str<N>`. -/
def arrayAsStrUnchecked := newGenericTotalPureBuiltin
  (fun n => ⟨[(Tp.u 8).array n], (.str n)⟩)
  (fun _ h![a] => arrayAsStr! a)

end KanLampe.Builtin
