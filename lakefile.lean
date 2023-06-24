import Lake
open Lake DSL

package math2001

lean_lib Library

@[default_target]
lean_lib Math2001 where
  moreLeanArgs := #["-Dlinter.unusedVariables=false", "-DwarningAsError=false", "-Dpp.unicode.fun=true"] -- pretty-prints `fun a ↦ b`
/-
# Figure out how to enable all these:

"-Dpush_neg.use_distrib=true", -- negates ¬(P ∧ Q) to (¬ P ∨ ¬ Q) 
"-DquotPrecheck=false",
"-DautoImplicit=false",
"-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
"-Dlinter.unusedVariables=false"] -- ignores unused variables
-/

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "750b7536599c7b0924e12fe79d0522b8554125c9"
require autograder from git "https://github.com/robertylewis/cs22-lean-autograder" @ "1c6119111649e9c18594be3b3722836025a96e86"

