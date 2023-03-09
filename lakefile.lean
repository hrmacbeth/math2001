import Lake
open Lake DSL

package math2001

@[default_target]
lean_lib Math2001 where
  moreLeanArgs := #["-DwarningAsError=true", "-Dpp.unicode.fun=true"] -- pretty-prints `fun a ↦ b`

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "9458c078999f9d8baf21d559545c17ac9ce8ce4d"
require autograder from git "https://github.com/robertylewis/cs22-lean-autograder" @ "1c9c67a3d0c3d5d5b159c37e3146323d3b6f4bb1"

