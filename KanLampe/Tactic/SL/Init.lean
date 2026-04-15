import Lean

/-!
# KanLampe.Tactic.SL.Init

Port of `Lampe.Tactic.SL.Init`.  Registers the `KanLampe.SL` trace
class used by the separation-logic tactic layer.
-/

initialize
  Lean.registerTraceClass `KanLampe.SL
