import data.int.modeq

namespace norm_num
open tactic

lemma not_false : (¬ false) = true := not_eq_of_eq_false rfl

lemma not_true : (¬ true) = false := not_eq_of_eq_true rfl

@[norm_num] meta def eval_not_Prop : expr → tactic (expr × expr)
| `(¬ false) := pure (`(true), `(not_false))
| `(¬ true) := pure (`(false), `(not_true))
| _ := failed

lemma modeq_ne {a b n : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (han : a < n) (hbn : b < n) (hab : a ≠ b) :
  (a ≡ b [ZMOD n]) = false :=
show (a % n = b % n) = false, by rwa [int.mod_eq_of_lt ha han, int.mod_eq_of_lt hb hbn, eq_false]

/-- `norm_num` extension to check modular equalities of small numbers.  Not needed in mathlib
because there are strictly more powerful tactics available. -/
@[norm_num] meta def eval_int_modeq : expr → tactic (expr × expr)
| `(%%a ≡ %%b [ZMOD %%n]) := do
      a₁ ← a.to_rat, 
      b₁ ← b.to_rat,
      n₁ ← n.to_rat,
      c ← mk_instance_cache `(int),
      (_, p_za) ← prove_le_rat c `(0) a 0 a₁, -- `0 ≤ a`
      (_, p_zb) ← prove_le_rat c `(0) b 0 b₁, -- `0 ≤ b`
      (_, p_an) ← prove_lt_rat c a n a₁ n₁, -- `a < n`
      (_, p_bn) ← prove_lt_rat c b n b₁ n₁, -- `0 ≤ b`
      if a₁ = b₁ then
        mk_mapp ``int.modeq.refl [n, a] >>= true_intro 
      else do
        (_, p_ab) ← prove_ne_rat c a b a₁ b₁, -- `a ≠ b`
        prod.mk `(false) <$> mk_app ``modeq_ne [p_za, p_zb, p_an, p_bn, p_ab]
| _ := failed

end norm_num

attribute [irreducible] int.modeq

example : ¬ (¬ true) := by norm_num1

example : ¬ (false) := by norm_num1

example : ¬ (0 ≡ 3 [ZMOD 4]) := by norm_num1

example : ¬ (0 + 6 ≡ 3 [ZMOD 15]) := by norm_num1

example : 3 ≡ 1 + 2 [ZMOD 4] := by norm_num1

-- the tactic is supposed to fail on "big" numbers
example : 4 ≡ 4 [ZMOD 4] := by success_if_fail { norm_num }; apply int.modeq.refl

