import KanLampe.Data.Digits
import KanLampe.Data.Integers
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace KanLampe

/--
The representation of the field prime for use in KanLampe's model of Noir's semantics.

In particular, this is ℕ constrained to being prime and _also_ being greater than 2 as we think
that there is no sane usage of Noir with a prime so low.  Additionally, we represent it internally
as `P + 1` in order to take advantage of `ZMod p` being defeq to `Fin p` if `p` is `Succ`.
-/
def Prime : Type := {P : ℕ // Nat.Prime (P + 1) ∧ P + 1 > 2}

namespace Prime

/--
Gets the value of the prime as a Nat, ensuring correctness under the representation.

Do not use `Prime.val` as this will provide a nat that is equal to `P - 1` due to our choice of
representation.
-/
def natVal (P : Prime) : ℕ := P.val + 1

/--
A helper to construct a concrete prime while handling the details of the prime representation.

It is recommended to use this function instead of trying to manually work with the details of the
`P + 1` representation we use internally.
-/
@[reducible]
def ofNat (p : ℕ) (is_prime : Nat.Prime p) (is_gt_two : p > 2) : Prime := ⟨p - 1, by
  kan_have h1 : 1 ≤ p := by
    kan_simp_only [gt_iff_lt] at is_gt_two
    kan_have hi : (1 : ℕ) < 2 := by kan_decide
    kan_have lt : 1 < p := lt_trans hi is_gt_two
    kan_exact Nat.le_of_lt lt
  kan_have h2 : p - 1 + 1 = p := Nat.sub_add_cancel h1
  kan_apply And.intro
  · kan_rw [h2]; kan_exact is_prime
  · kan_rw [h2]; kan_exact is_gt_two⟩

lemma prime_ne_two_pow_bits {prime : Prime} {bits : ℕ} (gt : prime.natVal > 2^bits)
  : prime.natVal ≠ 2^bits := by
  kan_intro heq
  kan_simp_only [heq] at gt
  kan_exact absurd gt (Nat.lt_irrefl _)

lemma two_pow_bits_lt_prime {prime : Prime} {bits : ℕ} (gt : prime.natVal > 2^bits)
  : 2^bits < prime.natVal := gt

/--
Certain operations in Noir are only correct when the prime has _at least_ a certain number of
bits in its representation.

Theorems that rely on this behavior should have a type-class constraint of `BitsGT p N` in their
signature, so they can only be used correctly if such an instance exists.

Note that this class is defined such that if a theorem relies on `BitsGT p M` but calls a theorem
that relies on `BitsGT p N` where `M > N`, the former instance will be sufficient.
-/
class BitsGT (prime : Prime) (bits : ℕ) where
  prime_gt : prime.natVal > 2^bits
  ne_two_pow_bits : prime.natVal ≠ 2 ^ bits := prime_ne_two_pow_bits prime_gt
  lt_prime : 2^bits < prime.natVal := two_pow_bits_lt_prime prime_gt

instance {p : Prime} : BitsGT p 0 where
  prime_gt := by
    kan_have hp : p.natVal > 2 := p.prop.right
    kan_simp_only [pow_zero]
    kan_linarith

instance {n : ℕ} {p : Prime} [hinst : BitsGT p (n + 1)] : BitsGT p n where
  prime_gt := by
    kan_simp_only [gt_iff_lt]
    kan_have hle : 2 ^ n ≤ 2 ^ (n + 1) :=
      Nat.pow_le_pow_right (Nat.le_of_lt Nat.one_lt_two) (Nat.le_succ _)
    kan_have hprime : p.natVal > 2 ^ (n + 1) := hinst.prime_gt
    kan_linarith

end Prime

def Fp (P : Prime) := ZMod P.natVal

instance {P : Prime} : DecidableEq (Fp P) := inferInstanceAs (DecidableEq (ZMod P.natVal))

instance {P : Prime} : Field (Fp P) :=
  let _ := Fact.mk P.prop.left
  inferInstanceAs (Field (ZMod (P.val + 1)))

instance {P : Prime} : NeZero (Prime.natVal P) := ⟨Nat.Prime.ne_zero P.prop.left⟩

def numBits (P : ℕ) : ℕ := Nat.log2 P + 1

def Fp.toBitsLE {P} n : Fp P → List.Vector (U 1) n := fun x =>
  let r : Radix := (2 : Radix)
  let v := x.val % r.val ^ n
  have hv : v < r.val ^ n :=
    Nat.mod_lt _ (Nat.pow_pos (by kan_decide : 0 < r.val))
  (RadixVec.toDigitsLE (r := r) (d := n) ⟨v, hv⟩).map BitVec.ofFin

lemma Fp.toBitsLE_eq_toDigitsLE {P} {n} {x : Fp P} :
    Fp.toBitsLE n x =
      (RadixVec.toDigitsLE (r := (2 : Radix)) (d := n)
        ⟨x.val % (2 : Radix).val ^ n,
          Nat.mod_lt _ (Nat.pow_pos (by kan_decide : 0 < (2 : Radix).val))⟩).map
        BitVec.ofFin := by
  kan_simp [Fp.toBitsLE]

lemma Fp.toBitsLE_eq_toDigitsLE_of_lt {P : Prime} {n : ℕ} {x : Fp P}
    (h : x.val < (2 : Radix).val ^ n) :
    Fp.toBitsLE n x =
      (RadixVec.toDigitsLE (r := (2 : Radix)) (d := n) ⟨x.val, h⟩).map BitVec.ofFin := by
  kan_have hmod : x.val % (2 : Radix).val ^ n = x.val := Nat.mod_eq_of_lt h
  kan_have e := Fp.toBitsLE_eq_toDigitsLE (x := x) (n := n)
  kan_simp_only [hmod] at e
  kan_exact e

def Fp.toBytesLE {P} n : Fp P → List.Vector (U 8) n := fun x =>
  let r : Radix := R256
  let v := x.val % r.val ^ n
  have hv : v < r.val ^ n :=
    Nat.mod_lt _ (Nat.pow_pos (by kan_decide : 0 < r.val))
  (RadixVec.toDigitsLE (r := r) (d := n) ⟨v, hv⟩).map BitVec.ofFin

lemma Fp.toBytesLE_eq_toDigitsLE {P} {n} {x : Fp P} :
    Fp.toBytesLE n x =
      (RadixVec.toDigitsLE (r := R256) (d := n)
        ⟨x.val % R256.val ^ n,
          Nat.mod_lt _ (Nat.pow_pos (by kan_decide : 0 < R256.val))⟩).map
        BitVec.ofFin := by
  kan_simp [Fp.toBytesLE]

lemma Fp.toBytesLE_eq_toDigitsLE_of_lt {P : Prime} {n : ℕ} {x : Fp P}
    (h : x.val < R256.val ^ n) :
    Fp.toBytesLE n x =
      (RadixVec.toDigitsLE (r := R256) (d := n) ⟨x.val, h⟩).map BitVec.ofFin := by
  kan_have hmod : x.val % R256.val ^ n = x.val := Nat.mod_eq_of_lt h
  kan_have e := Fp.toBytesLE_eq_toDigitsLE (x := x) (n := n)
  kan_simp_only [hmod] at e
  kan_exact e

def Fp.ofBytesLE {P : Prime} : List (U 8) → Fp P := fun bytes =>
  ((RadixVec.ofLimbsLE' 256 (bytes.map BitVec.toNat) : ℕ) : Fp P)

theorem Fp.cast_self {P : Prime} {p : Fp P} : (p.cast : Fp P) = p := by
  (kan_unfold ZMod.cast)
  kan_simp_only [Prime.natVal]
  kan_apply ZMod.natCast_zmod_val

lemma Fp.eq_of_val_eq {P : Prime} {x y : Fp P} : x.val = y.val → x = y := by
  kan_simp [ZMod.val, Prime.natVal]
  kan_exact Fin.eq_of_val_eq

end KanLampe
