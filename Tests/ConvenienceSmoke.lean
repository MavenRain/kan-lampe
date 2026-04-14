import KanLampe.Convenience

/-!
# Smoke tests for KanLampe.Convenience

One example per convenience tactic.  Each proof must elaborate
without invoking any non-kan-tactics primitive.
-/

set_option autoImplicit false

namespace KanLampe.Tests.ConvenienceSmoke

/-! ## kan_decide -/

example : (1 : Nat) + 1 = 2 := by kan_decide
example : (3 : Nat) ≤ 5 := by kan_decide
example : ∀ n : Fin 4, n.val < 4 := by kan_decide

/-! ## kan_ring -/

example (a b c : Nat) : a * (b + c) = a * b + a * c := by kan_ring
example (a : Nat) : a * 1 + 0 = a := by kan_ring

/-! ## kan_ring on Int -/

example (a b c : Int) : a * (b + c) = a * b + a * c := by kan_ring

/-! ## kan_omega -/

example : (1 : Nat) + 1 ≤ 3 := by kan_omega
example (n : Nat) : n + 0 = n := by kan_omega
example : (5 : Nat) + 3 = 8 := by kan_omega

/-! ## kan_aesop -/

example (p : Prop) (h : p) : p := by kan_aesop
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by kan_aesop
example (p : Prop) : p → p := by kan_aesop

/-! ## kan_bv_decide -/

example : (5 : BitVec 8) = 5 := by kan_bv_decide
example : (3 : BitVec 8) + 4 = 7 := by kan_bv_decide

/-! ## kan_assumption -/

example (p : Prop) (h : p) : p := by kan_assumption

end KanLampe.Tests.ConvenienceSmoke
