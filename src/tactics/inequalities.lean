/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import tactic
import tactic.positivity

namespace tactic

-- Just the goal-acting part of `norm_num`
meta def norm_num.goal : tactic unit :=
solve1 $ do
  -- a ← get_eqn_lemmas_for tt `ge,
  -- b ← a.mmap mk_const,
  -- try (b.mmap rewrite_target),
  (new_t, pr) ← target >>= norm_num.derive' norm_num.derive.step,
  replace_target new_t pr,
  triv

@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }

@[user_attribute]
meta def strict_mono_rules : user_attribute :=
{ name := `strict_mono_rules,
  descr := "lemmas usable to prove strict monotonicity" }

-- order matters here: need division and subtraction to be recognized as such, prioritized over
-- multiplications/additions which are definitionally equal
attribute [mono_rules] 
  le_add_of_nonneg_right le_add_of_nonneg_left
  pow_le_pow_of_le_left div_le_div_of_le
  mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right
  mul_le_mul_of_nonpos_left mul_le_mul_of_nonpos_right
  sub_le_sub add_le_add
  
-- order matters here: need division and subtraction to be recognized as such, prioritized over
-- multiplications/additions which are definitionally equal
attribute [strict_mono_rules] pow_lt_pow_of_lt_left div_lt_div_of_lt mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right sub_lt_sub_left sub_lt_sub_right add_lt_add_left add_lt_add_right
  lt_add_of_pos_right lt_add_of_pos_left

meta def check_same_head (a b : expr) : tactic unit :=
do
  guard a.is_app,
  guard b.is_app,
  guard (a.get_app_fn = b.get_app_fn),
  guard ¬ (a.is_app_of `bit0), -- ad hoc check that we're not forcing a `bit0` to addition
  guard ¬ (a.is_app_of `bit1) -- ad hoc check that we're not forcing a `bit1` to addition

meta def apply_tacs_if_ineq (mono_tacs strict_mono_tacs : list (tactic expr)) : tactic unit := do
  t_typ ← target,
  match t_typ with
  | `(has_le.le %%a %%b) := 
    do applyc `le_refl <|>
      --  do check_same_head a b,
          apply_list_expr {md := reducible} mono_tacs
  | `(ge %%a %%b) :=
    do applyc `le_refl <|>
       do --check_same_head a b,
          apply_list_expr {md := reducible} mono_tacs
  | `(has_lt.lt %%a %%b) :=
    do --check_same_head a b,
       apply_list_expr {md := reducible} strict_mono_tacs
  | `(gt %%a %%b) :=
    do --check_same_head a b,
       apply_list_expr {md := reducible} strict_mono_tacs
  | _ := fail "not an inequality goal"
  end

meta def ineq_congr_weak : tactic unit := do
  mono_exprs ← lock_tactic_state $ resolve_attribute_expr_list `mono_rules,
  strict_mono_exprs ← lock_tactic_state $ resolve_attribute_expr_list `strict_mono_rules,
  iterate_at_most_on_all_goals 50 (apply_tacs_if_ineq mono_exprs strict_mono_exprs)

meta def ineq_congr : tactic unit := do
  ineq_congr_weak,
  all_goals' (try tactic.interactive.positivity)

meta def add_nonstricts (l : list expr) : tactic (list expr) :=
l.mfoldl (λ t h, do 
  h_typ ← infer_type h,
  match h_typ with
  | `(has_lt.lt %%a %%b) := do 
    h_nonstrict ← mk_app `le_of_lt [h],
    return (h_nonstrict :: h :: t)
  | `(gt %%a %%b) := do 
    h_nonstrict ← mk_app `le_of_lt [h],
    return (h_nonstrict :: h :: t)
  | _ := return (h :: t)
  end) []

/-- version of `ineq_tac` which only applies the provided hypotheses at the end -/
meta def ineq_tac (hs : list pexpr) : tactic unit := solve1 $
do ineq_congr_weak,
  let local_apply : expr → tactic unit := λ h, solve1 $ tactic.interactive.concat_tags (tactic.apply h {md := reducible}),
  -- TODO: make the next line complain if an irrelevant hypothesis is provided
  all_goals' (hs.mmap i_to_expr_for_apply >>= add_nonstricts >>= list.foldr (λ H, (<|>) (local_apply H)) (pure ())),
  all_goals' (try tactic.interactive.positivity)

-- /-- version of `ineq_tac` which alternates applying the lemmas and the provided hypotheses, if necessary -/
-- meta def ineq_tac (hs : list pexpr) : tactic unit := do
--   attr_exprs ← lock_tactic_state $ resolve_attribute_expr_list `mono_rules,
--   l ← hs.mmap i_to_expr_for_apply >>= add_nonstricts,
--   let args_exprs := (l.map pure) ++ attr_exprs,
--   iterate_at_most_on_subgoals 50 (apply_list_expr {} args_exprs),
--   all_goals' nonnegativity

meta def norm_num1' : tactic unit := norm_num1 (norm_num.derive.step) (interactive.loc.ns [none])

meta def abel_aux : tactic unit := do
  success ← replace_at (abel.normalize semireducible abel.normalize_mode.term) [] tt,
  pure ()

namespace interactive

setup_tactic_parser

meta def ineq_congr : tactic unit := tactic.ineq_congr

meta def ineq_tac (hs : parse pexpr_list_or_texpr) : tactic unit := tactic.ineq_tac hs

-- This tactic is a deliberately weakened version of the mathlib tactic `linarith`.
meta def addarith (hyp : parse parser.pexpr) : tactic unit :=
tactic.linarith ff tt [hyp]
{ discharger := `[try { simp only [one_mul, neg_mul] }, abel_aux, try { simp only [zsmul_eq_mul] }, try { push_cast }, norm_num1'] }

/-
Note: `addarith` fails in an unprincipled way on some goals with more than one hypothesis, e.g.
because of the main linarith tactic turning (a + a)'s into (2a)'s.  For example,

example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
by addarith [h1, h2]

example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) (h3 : x + x = 2 * x) : 
  x = 5 :=
by addarith [h1, h2, h3]

-/

end interactive

end tactic
