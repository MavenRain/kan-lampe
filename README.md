# kan-lampe

A port of [reilabs/lampe](https://github.com/reilabs/lampe) (Lean
formalization of Noir ZK DSL semantics) that proves everything using
only the 9-family spanning set of
[MavenRain/kan-tactics](https://github.com/MavenRain/kan-tactics).

## Thesis

Every tactic used in Lampe's proof script, including decision
procedures like `omega`, `decide`, `ring`, `aesop`, and `bv_decide`,
can be re-expressed as an automation layer over the 9 primitive
`KanExtensionKind` variants in kan-tactics.  Those 9 primitives are
in bijection with the term-forming rules of intuitionistic type
theory with inductive types, so every closed proof term factors
through them.

See [`docs/SpanningSet.md`](docs/SpanningSet.md) for the
correspondence and the argument.

## Layout

```
KanLampe/
  Convenience/
    Decide.lean       kan_decide
    Ring.lean         kan_ring
    Omega.lean        kan_omega
    Aesop.lean        kan_aesop
    BvDecide.lean     kan_bv_decide
  Convenience.lean    re-export of the above
  (ported lampe modules)
```

Each convenience tactic is a macro that elaborates to a sequence of
core kan-tactics primitives.  No convenience tactic introduces a
new `KanExtensionKind`; they are all derived.

## Building

```sh
lake build
```

Requires the kan-tactics repo at `../kan-tactics` (sibling directory).

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
