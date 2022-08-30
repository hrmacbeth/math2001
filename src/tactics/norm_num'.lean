import tactic.norm_num

open tactic

namespace norm_num

/-- Evaluates some extra numeric operations on `nat` and `int`, specifically
`nat.succ`, `/` and `%`, and `∣` (divisibility). -/
meta def eval_nat_int_ext' : expr → tactic (expr × expr)
| e@`(nat.succ _) := do
  ic ← mk_instance_cache `(ℕ),
  (_, _, ep) ← prove_nat_succ ic e,
  return ep
| `(%%a / %%b) := do
  c ← infer_type a >>= mk_instance_cache,
  prod.snd <$> prove_div_mod c a b ff
| `(%%a % %%b) := do
  c ← infer_type a >>= mk_instance_cache,
  prod.snd <$> prove_div_mod c a b tt
| `(int.to_nat %%a) := do
  n ← a.to_int,
  ic ← mk_instance_cache `(ℤ),
  if n ≥ 0 then do
    nc ← mk_instance_cache `(ℕ),
    (_, _, b, p) ← prove_nat_uncast ic nc a,
    pure (b, `(int_to_nat_pos).mk_app [a, b, p])
  else do
    a ← match_neg a,
    (_, p) ← prove_pos ic a,
    pure (`(0), `(int_to_nat_neg).mk_app [a, p])
| `(int.nat_abs %%a) := do
  n ← a.to_int,
  ic ← mk_instance_cache `(ℤ),
  nc ← mk_instance_cache `(ℕ),
  if n ≥ 0 then do
    (_, _, b, p) ← prove_nat_uncast ic nc a,
    pure (b, `(nat_abs_pos).mk_app [a, b, p])
  else do
    a ← match_neg a,
    (_, _, b, p) ← prove_nat_uncast ic nc a,
    pure (b, `(nat_abs_neg).mk_app [a, b, p])
| `(int.neg_succ_of_nat %%a) := do
  na ← a.to_nat,
  ic ← mk_instance_cache `(ℤ),
  nc ← mk_instance_cache `(ℕ),
  let nb := na + 1,
  (nc, b) ← nc.of_nat nb,
  (nc, p₁) ← prove_add_nat nc a `(1) b,
  (ic, c) ← ic.of_nat nb,
  (_, _, _, p₂) ← prove_nat_uncast ic nc c,
  pure (`(-%%c : ℤ), `(neg_succ_of_nat).mk_app [a, b, c, p₁, p₂])
| _ := failed

/-- This version of `derive` does not fail when the input is already a numeral -/
meta def derive.step' (e : expr) : tactic (expr × expr) :=
eval_field e <|> eval_pow e <|> eval_ineq e <|> eval_cast e <|> eval_nat_int_ext' e

end norm_num

open norm_num interactive interactive.types


/-- Normalize numerical expressions. Supports the operations
`+` `-` `*` `/` and `^` over numerical types such as
`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`,
where `A` and `B` are numerical expressions. -/
meta def tactic.interactive.norm_num'
  (loc : parse location) : tactic unit :=
do ns ← loc.get_locals,
   success ← tactic.replace_at (norm_num.derive' derive.step') ns loc.include_goal,
   when loc.include_goal $ try tactic.triv,
   when (¬ ns.empty) $ try tactic.contradiction,
   monad.unlessb success $ done <|> fail "norm_num failed to simplify"

#exit

/- Do we want the simp-ing behaviour in mathlib `norm_num`? -/

-- old docstring on `norm_num1'`:
/-- Basic version of `norm_num` that does not call `simp`. It uses the provided `step` tactic
to simplify the expression; use `get_step` to get the default `norm_num` set and `derive.step` for
the basic builtin set of simplifications. -/

-- old docstring on `interactive.norm_num1'`:
/-- Basic version of `norm_num'` that does not call `simp`. -/

/-- Normalize numerical expressions. It uses the provided `step` tactic to simplify the expression;
use `get_step` to get the default `norm_num` set and `derive.step` for the basic builtin set of
simplifications. -/
meta def tactic.norm_num' 
  (hs : list simp_arg_type) (l : interactive.loc) : tactic unit :=
repeat1 $ orelse' (tactic.norm_num1 derive.step' l) $
interactive.simp_core {} (tactic.norm_num1 derive.step' (interactive.loc.ns [none]))
  ff (simp_arg_type.except ``one_div :: hs) [] l >> skip

/-- Normalize numerical expressions. Supports the operations
`+` `-` `*` `/` and `^` over numerical types such as
`ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`,
where `A` and `B` are numerical expressions. -/
meta def norm_num' (hs : parse simp_arg_list) (l : parse location) : tactic unit :=
tactic.norm_num' hs l
