/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.inequalities
import library.arithmetic2


example {n : ℕ} : n ^ 2 ≠ 2 :=
begin
  have hn : n ≤ 1 ∨ 2 ≤ n := le_or_lt n 1,
  cases hn with hn hn,
  apply ne_of_lt,
  have : 0 ≤ n := sorry, -- soon will be built into `positivity`
  calc n ^ 2 ≤ 1 ^ 2 : by ineq_tac [hn]
  ... < 2 : by norm_num,
  apply ne_of_gt,
  calc 2 < 2 ^ 2 : by norm_num
  ... ≤ n ^ 2 : by ineq_tac [hn],
end


example {a b : ℝ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin
  have ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0,
  cases ha with ha ha,
  right,
  apply eq_zero_of_mul_neg_eq_zero a,
  apply h,
  apply ha,
  cases ha with ha ha,
  left,
  apply ha,
  right,
  apply eq_zero_of_mul_pos_eq_zero a,
  apply h,
  apply ha,
end


example {n : ℤ} : n ^ 2 ≠ 2 :=
begin
  have hn0 : n ≤ 0 ∨ 1 ≤ n := le_or_lt n 0,
  cases hn0 with hn0 hn0,
  { have : 0 ≤ - n,
    addarith hn0,
    have hn : -n ≤ 1 ∨ 2 ≤ -n := le_or_lt (-n) 1,
    cases hn,
    { apply ne_of_lt,
      calc n ^ 2 = (-n) ^ 2 : by ring
      ... ≤ 1 ^ 2 : by ineq_tac [hn]
      ... < 2 : by norm_num },
    { apply ne_of_gt,
      calc 2 < 2 ^ 2 : by norm_num
      ... ≤ (-n) ^ 2 : by ineq_tac [hn]
      ... = n ^ 2 : by ring } },
  { have hn : n ≤ 1 ∨ 2 ≤ n := le_or_lt n 1,
    cases hn with hn hn,
    { apply ne_of_lt,
      calc n ^ 2 ≤ 1 ^ 2 : by ineq_tac [hn]
      ... < 2 : by norm_num },
    { apply ne_of_gt,
      calc 2 < 2 ^ 2 : by norm_num
      ... ≤ n ^ 2 : by ineq_tac [hn] } },
end


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 :=
begin
  have hx' : x - 1 = 0 ∨ x - 2 = 0,
  apply eq_zero_or_eq_zero_of_mul_eq_zero,
  sorry,
  sorry,
end


example {a : ℝ} (ha : a ^ 2 = 0) : a = 0 :=
begin
  sorry,
end


example {n : ℕ} : n ^ 2 ≠ 7 :=
begin
  sorry,
end


example {a : ℝ} (ha : a ^ 3 = 0) : a = 0 :=
begin
  sorry,
end


example {x y : ℝ} (hxy : x ^ 2 + 5 * y = y ^ 2 + 5 * x) : x = y ∨ x + y = 5 :=
begin
  sorry,
end
