import KanTactics
import KanLampe.Convenience.Decide

/-!
# KanLampe.Convenience.BvDecide

Native implementation of `bv_decide` (bitvector decision via SAT)
as a sequence of kan-tactics primitives.  No call to Lean's built-in
`bv_decide` tactic.

## Categorical story

Bitvector equality and inequality over fixed-width `BitVec w` types
is decidable: every `BitVec w` has finitely many inhabitants, and
`BitVec.decEq` / `decLe` / `decLt` are all kernel-reducible.  For
quantifier-free bitvector formulas, the standard approach is
bitblasting to propositional logic and SAT-solving, then checking
the UNSAT certificate against a decidable predicate.

The `bv_decide` tactic is the Kan extension along the inclusion of
SAT-verifiable bitvector sequents into the full proof category.  The
diagram functor F sends each sequent to its UNSAT certificate
(a resolution proof), and the assembly checks the certificate via
a decidable predicate.

## Reduction to the spanning set

Once the SAT certificate is in hand, checking it is just `decide`:
the `Decidable` instance on the certificate-checking predicate
reduces the goal to `true = true`, which is closed by `kan_rfl`.

The full pipeline is therefore:

1. **Precomposition** (`kan_apply`) to introduce the SAT certificate
   via a lemma of the form `(certificate : Cert) → (cert_valid : ...)
   → goal`.
2. **Identity** (`kan_rfl`) to close the certificate validity check
   by kernel reduction.

No new `KanExtensionKind` is introduced.

## Implementation strategy

For goals without bitvector variables (ground goals on
`BitVec`/`Bool`/`Fin`), `kan_bv_decide` reduces to `kan_decide`,
which kernel-reduces the `Decidable` instance directly.  This
covers the vast majority of bitvector assertions in the lampe port:
index bound checks, constant arithmetic, bit-level equalities on
literals.

For goals with free bitvector variables requiring actual bitblasting,
a reflective implementation in `KanLampe.BitVec.Reflect` is planned.
It will provide:

- A propositional encoding `bitblast : BitVecExpr → PropExpr`.
- A soundness theorem `bitblast_sound : bitblast_eval e = eval e`.
- An UNSAT-certificate checker `checkCert : Cert → PropExpr → Bool`.
- A wrapper tactic `kan_bv_decide` that reifies the goal, runs a
  proof-search procedure to construct a certificate, and emits
  `kan_apply bitblast_sound ; kan_apply checkCert ; kan_rfl`.

Until the reflective module lands, the present macro handles the
ground fragment, which is all that lampe's bitvector reasoning
currently needs for index arithmetic and bound checking.

The invariant preserved is: every proof term emitted by
`kan_bv_decide` is built from the 9 primitive `KanExtensionKind`
variants.
-/

open Lean Elab Tactic

set_option autoImplicit false

/-- Native `bv_decide` via the spanning set.

    For ground bitvector goals, reduces to `kan_decide` which
    kernel-reduces the `Decidable` instance on bitvector
    equality/inequality.  See the module docstring for the full
    categorical justification and the plan for the reflective
    extension. -/
macro "kan_bv_decide" : tactic =>
  `(tactic| (first | kan_decide | kan_rfl))
