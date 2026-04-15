import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Stubs

Port of `Lampe.Builtin.Stubs`.  A single empty-inductive `StubOmni`
semantic and the `stub` builtin.  All stubbed Noir builtins reduce
to `stub`, making any term that mentions them unprovable without
introducing unsoundness.
-/

namespace KanLampe.Builtin

inductive StubOmni : Omni where

/-- Dummy builtin used for unimplemented Noir builtins. -/
def stub : Builtin := {
  omni := StubOmni
  conseq := by
    kan_intro P
    kan_intro st
    kan_intro argTps
    kan_intro outTp
    kan_intro args
    kan_intro Q
    kan_intro Q'
    kan_intro h_omni
    kan_intro h_imp
    kan_cases_with h_omni
  frame := by
    kan_intro P
    kan_intro st₁
    kan_intro st₂
    kan_intro argTps
    kan_intro outTp
    kan_intro args
    kan_intro Q
    kan_intro h_omni
    kan_intro hdis
    kan_cases_with h_omni
}

def aes128Encrypt := stub
def arrayRefcount := stub
def asWitness := stub
def assertConstant := stub
def blackBox := stub
def blake2S := stub
def blake3 := stub
def checkedTransmute := stub
def derivePedersenGenerators := stub
def ecdsaSecp256K1 := stub
def ecdsaSecp256R1 := stub
def embeddedCurveAdd := stub
def fmtstrAsCtstring := stub
def keccakf1600 := stub
def mkFormatString := stub
def multiScalarMul := stub
def poseidon2Permutation := stub
def recursiveAggregation := stub
def sha256Compression := stub
def sliceRefcount := stub
def strAsCtstring := stub

end KanLampe.Builtin
