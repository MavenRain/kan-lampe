import Mathlib.Tactic.CasesM
import KanLampe.Convenience

/-!
# KanLampe.Tactic.IntroCases

`kan_intro_cases`: introduce all hypotheses, then destructure every
conjunction or existential in the local context.

Implementation: thin wrapper around `kan_intros` and Mathlib's
`casesm*`.  The proof term produced is the same as repeated
`kan_cases` applications (Decomposition primitive), routed through
the casesm pattern engine for selection.  No new
`KanExtensionKind` is introduced.
-/

namespace KanLampe

macro "kan_intro_cases" : tactic =>
  `(tactic| (kan_intros; try casesm* _ ∧ _, ∃ _, _))

end KanLampe
