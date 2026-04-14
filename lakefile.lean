import Lake
open Lake DSL

package «kan-lampe» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]
  testDriver := "Tests"

require «kan-tactics» from ".." / "kan-tactics"
require "leanprover-community" / "mathlib" @ git "v4.30.0-rc1"

@[default_target]
lean_lib «KanLampe» where
  roots := #[`KanLampe]

lean_lib Tests where
  globs := #[.submodules `Tests]
