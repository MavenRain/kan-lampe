import KanTactics
import Mathlib.Tactic.Linarith

/-!
# KanLampe.Convenience.Linarith

Native implementation of `linarith` (linear arithmetic over ordered
(semi)rings) as a convenience tactic over the 9 primitive
`KanExtensionKind` variants.

## Categorical story

Linear arithmetic sequents are a decidable subcategory of the proof
category for linearly ordered (semi)rings.  A `linarith` certificate
is a nonneg linear combination of hypotheses that witnesses the goal.
The certificate is built from:

- **Identity** (`kan_exact`) to name hypotheses.
- **Precomposition** (`kan_apply`) to apply linearity lemmas
  (`add_le_add`, `mul_nonneg`, etc.).

No new `KanExtensionKind` is introduced.

## Implementation

Delegates to Mathlib's `linarith` tactic as a proof-term generator.
This is a performance choice per the SpanningSet.md "pragmatic
automation" section: the proof term is in the image of the 9
families regardless of how it is computed.
-/

open Lean Elab Tactic

set_option autoImplicit false

/-- Native `linarith` via the spanning set.

    Delegates to Mathlib's `linarith` as a proof-term generator. -/
elab "kan_linarith" : tactic => do
  evalTactic (← `(tactic| linarith))

/-- `linarith` with extra lemmas fed as hypotheses. -/
elab "kan_linarith " "[" lemmas:term,* "]" : tactic => do
  evalTactic (← `(tactic| linarith [$lemmas,*]))
