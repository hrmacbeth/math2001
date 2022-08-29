/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.int.modeq
import tactic.fin_cases
import tactic.interactive
import tactic.norm_cast
-- import tactics.apply_rules_var

@[user_attribute]
meta def mod_rules : user_attribute :=
{ name := `mod_rules,
  descr := "lemmas usable to prove modular arithmetic facts" }

/-- Congruence lemmas (currently an incomplete list) -/
attribute [mod_rules] int.modeq.add_right int.modeq.add_left int.modeq.add int.modeq.sub_right
  int.modeq.sub_left int.modeq.sub int.modeq.mul_left int.modeq.mul_right int.modeq.neg int.modeq.pow
  int.modeq.refl

/-- Lemma needed for finiteneness arguments in `mod_cases`. -/
lemma int.exists_unique_modeq_mem_range (a : ℤ) (b : ℕ) (hb : 0 < b) :
  ∃ z ∈ finset.range b, a ≡ z [ZMOD b] :=
begin
  obtain ⟨a₀, ha₀, ha₀n⟩ := int.exists_unique_equiv_nat a (by exact_mod_cast hb : (0:ℤ) < b),
  norm_cast at ha₀,
  refine ⟨a₀, finset.mem_range.mpr ha₀, _⟩,
  apply int.modeq.symm,
  exact ha₀n
end

namespace tactic

meta def add_symms (l : list expr) : tactic (list expr) :=
l.mfoldl (λ t h, do 
  h_typ ← infer_type h,
  match h_typ with
  | `(int.modeq %%a %%b %%c) := do 
    h_symm ← mk_app `int.modeq.symm [h],
    return (h_symm :: h :: t)
  | _ := return (h :: t)
  end) []

meta def mod_rw (hs : list pexpr) : tactic unit := do
  attr_exprs ← lock_tactic_state $ resolve_attribute_expr_list `mod_rules,
  l ← hs.mmap i_to_expr_for_apply >>= add_symms,
  let args_exprs := (l.map pure) ++ attr_exprs,
  iterate_at_most_on_subgoals 50 (apply_list_expr {} args_exprs)

/-
To make this work using `apply_rules`

* `assumption!` which also uses symms of assumptions
* flag for apply_rules which uses `assumption!`
* (possibly just in own code) wrapper for apply_rules which uses `mod_rules` and symm flag
-/

meta def mod_cases (n : expr) (p' : ℕ) (H : name) : tactic unit :=
do p ← expr.of_nat `(ℕ) p',
  ic ← mk_instance_cache `(ℕ),
  (_, hh) ← norm_num.prove_pos_nat ic p,
  w ← mk_app `int.exists_unique_modeq_mem_range [n, p, hh],
  [(_, [_, hw])] ← tactic.cases w,
  [(_, [hk, _])] ← tactic.cases hw [`_, H],
  tactic.fin_cases_at none none hk,
  () <$ all_goals (do
    H' ← get_local H,
    () <$ replace_at norm_cast.derive [H'] ff)

setup_tactic_parser

namespace interactive

meta def mod_rw (hs : parse pexpr_list_or_texpr) : tactic unit :=
tactic.mod_rw hs

meta def mod_cases
  (n : parse parser.pexpr)
  (p : parse small_nat)
  (h : parse (tk "with" *> ident)?) : tactic unit :=
do n' ← to_expr ``(%%n : ℤ),
   tactic.mod_cases n' p (h.get_or_else `h)

end interactive
end tactic
