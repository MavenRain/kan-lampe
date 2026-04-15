import KanLampe.Builtin.Basic

/-!
# KanLampe.Builtin.Runtime

Port of `Lampe.Builtin.Runtime`.  Exposes `isUnconstrained`, which
always returns `false` so that we can reason about the code.
-/

namespace KanLampe.Builtin

/-- Returns whether the execution is performed in an unconstrained
context.  We always return `false` because otherwise we would be
unable to reason about the code. -/
def isUnconstrained := newTotalPureBuiltin
  ([], .bool)
  (fun _ => false)

end KanLampe.Builtin
