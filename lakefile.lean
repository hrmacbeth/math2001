import Lake
open Lake DSL

package math2001 where
  moreServerArgs := #[
    "-Dlinter.unusedVariables=false", -- ignores unused variables
    "-DquotPrecheck=false",
    "-DwarningAsError=false",
    "-Dpp.unicode.fun=true"  -- pretty-prints `fun a ↦ b`
  ]

lean_lib Library

@[default_target]
lean_lib Math2001 where
  globs := #[.submodules `Math2001]
  moreLeanArgs := #[
    "-Dlinter.unusedVariables=false", -- ignores unused variables
    "-DquotPrecheck=false",
    "-DwarningAsError=false",
    "-Dpp.unicode.fun=true"  -- pretty-prints `fun a ↦ b`
  ]

/-
want also
"-Dpush_neg.use_distrib=true", -- negates ¬(P ∧ Q) to (¬ P ∨ ¬ Q)
but currently only Lean core options can be set in lakefile
-/

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ s!"v{Lean.versionString}"
require Duper from git "https://github.com/hrmacbeth/duper" @ "main"
require autograder from git "https://github.com/robertylewis/lean4-autograder-main" @ "864b34ce06d8536aec0c38e57448c17d1f83572a"
