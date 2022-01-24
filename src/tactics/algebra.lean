/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import tactic

namespace tactic

meta def add_both_sides (q : expr) (hyp : expr) : tactic unit :=
do t ← infer_type hyp,
   pf ← match t with
   | `(%%l = %%r) := do
      ltp ← infer_type l,
      add_fn ← mk_mapp `has_add.add [ltp, none, q],
      mk_congr_arg add_fn hyp
   | _ := fail! "failed to add {q} to {hyp}"
   end,
   tactic.clear hyp,
   hyp ← note hyp.local_pp_name none pf,
   -- let's try to force β-reduction at `hyp`
   try $ tactic.dsimp_hyp hyp simp_lemmas.mk [] { eta := false, beta := true }

meta def mul_both_sides (q : expr) (hyp : expr) : tactic unit :=
do t ← infer_type hyp,
   pf ← match t with
   | `(%%l = %%r) := do
      ltp ← infer_type l,
      mul_fn ← mk_mapp `has_mul.mul [ltp, none, q],
      mk_congr_arg mul_fn hyp
   | _ := fail! "failed to multiply {q} to {hyp}"
   end,
   tactic.clear hyp,
   hyp ← note hyp.local_pp_name none pf,
   -- let's try to force β-reduction at `hyp`
   try $ tactic.dsimp_hyp hyp simp_lemmas.mk [] { eta := false, beta := true }

namespace interactive

setup_tactic_parser

meta def substitute (q : parse rw_rules) (l : parse location) (cfg : rewrite_cfg := {}) :
  tactic unit :=
tactic.solve1 (rw q l cfg) <|> fail "These are not equivalent up to substitution."

meta def add_both_sides (q : parse texpr) (locs : parse location) : tactic unit :=
do q_expr ← to_expr q,
   locs.apply (tactic.add_both_sides q_expr) skip

meta def mul_both_sides (q : parse texpr) (locs : parse location) : tactic unit :=
do q_expr ← to_expr q,
   locs.apply (tactic.mul_both_sides q_expr) skip

meta def exact_mod_ring (hyp : parse texpr) : tactic unit :=
tactic.solve1 $
do convert none hyp (some 1),
   all_goals $ ring1 none

end interactive
end tactic