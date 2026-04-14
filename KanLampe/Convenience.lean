import KanLampe.Convenience.SimpByName
import KanLampe.Convenience.Decide
import KanLampe.Convenience.Ring
import KanLampe.Convenience.Omega
import KanLampe.Convenience.Aesop
import KanLampe.Convenience.BvDecide
import KanLampe.Convenience.Linarith
import KanLampe.Convenience.SimpAll
import KanLampe.Convenience.Structural

/-!
# KanLampe.Convenience

Convenience tactics for the lampe port.  Every tactic in this
namespace is a macro that expands to a sequence of the 9 core
`KanExtensionKind` primitives from `KanTactics.Tactic.Core`.

None of these tactics introduces a new Kan extension kind.  They
are automation layers over the spanning set, in the sense made
precise in `docs/SpanningSet.md`.
-/
