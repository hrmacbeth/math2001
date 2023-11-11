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

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "76efc30c6ac851df9dfbf6440f6371ee57bf2961"
require Duper from git "https://github.com/hrmacbeth/duper" @ "c7d77c614e8826cf820f542da7ccebe668b0c85d"
require autograder from git "https://github.com/robertylewis/cs22-lean-autograder" @ "d29084f86176500452c7bc9b9e27ad55342d687c"
