/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import tactic.norm_num
import data.int.modeq

namespace norm_num
open tactic

/-- This is similar to `norm_num.derive.step`, but we have disabled its ability to check
divisibility/remainders. -/
meta def derive.step' (e : expr) : tactic (expr × expr) :=
eval_field e <|> eval_pow e <|> eval_ineq e <|> eval_cast e -- <|> eval_zmod e

end norm_num

namespace tactic.interactive
open interactive interactive.types

meta def small_nums (loc : parse location) : tactic unit :=
tactic.norm_num1 norm_num.derive.step' loc

end tactic.interactive