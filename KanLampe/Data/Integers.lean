import KanLampe.Convenience
import Mathlib.Data.Fintype.Basic

namespace KanLampe

abbrev U (n : Nat) := BitVec (n)
abbrev I (n : Nat) := BitVec (n)

instance {n : Nat} : DecidableEq (U n) := inferInstanceAs (DecidableEq (BitVec _))

instance {n : Nat} : DecidableEq (I n) := inferInstanceAs (DecidableEq (BitVec _))

instance {n : Nat} : Repr (U n) where
  reprPrec := fun a _ => a.toNat.repr

example : (BitVec.ofInt 8 (-128)).sdiv (BitVec.ofInt 8 (-1)) = -128 := by kan_rfl

instance {n : Nat} : Repr (I n) where
  reprPrec := fun a _ => a.toInt.repr

/-- A proposition that checks whether the integer `val` can be represented by a `w`-width bit
vector in 2s complement -/
abbrev bitsCanRepresent (w : Nat) (val : Int) := val < 2^(w-1) ∧ val ≥ -2^(w-1)

end KanLampe
