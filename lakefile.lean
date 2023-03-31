import Lake
open Lake DSL

package math2001

@[default_target]
lean_lib Math2001 where
  moreLeanArgs := #["-DwarningAsError=true", "-Dpp.unicode.fun=true"] -- pretty-prints `fun a ↦ b`

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "9458c078999f9d8baf21d559545c17ac9ce8ce4d"
require autograder from git "https://github.com/robertylewis/cs22-lean-autograder" @ "1c6119111649e9c18594be3b3722836025a96e86"

