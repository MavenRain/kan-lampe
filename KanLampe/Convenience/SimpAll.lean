import KanTactics

/-!
# KanLampe.Convenience.SimpAll

Convenience wrapper for `simp_all` (simplification across goal and
all hypotheses) as a tactic over the 9 primitive `KanExtensionKind`
variants.

## Categorical story

Same as the Normalize family: transport in the sub-groupoid of the
simp lemma set, applied simultaneously to the goal and every
hypothesis in context.

No new `KanExtensionKind` is introduced.

## Implementation

Delegates to Lean's built-in `simp_all` tactic.
-/

open Lean Elab Tactic

set_option autoImplicit false

/-- Native `simp_all` via the spanning set. -/
elab "kan_simp_all" : tactic => do
  evalTactic (← `(tactic| simp_all))

/-- `simp_all` with extra lemmas. -/
macro "kan_simp_all " "[" lemmas:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp_all [$[$lemmas:simpLemma],*])
