/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.inequalities
import library.arithmetic2

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 :=
begin
  have hx' : x - 1 = 0 ∨ x - 2 = 0,
  apply eq_zero_or_eq_zero_of_mul_eq_zero,
  calc (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 : by ring
  ... = 0 : by rw [hx],
  cases hx' with hx' hx',
  left,
  addarith [hx'],
  right,
  addarith [hx'],
end

example {a : ℝ} (ha : a ^ 2 = 0) : a = 0 :=
begin
  have h2 : a = 0 ∨ a = 0,
  apply eq_zero_or_eq_zero_of_mul_eq_zero,
  calc a * a = a ^ 2 : by ring
  ... = 0 : ha,
  cases h2 with h2 h2,
  rw h2,
  rw h2,
end

example {n : ℕ} : n ^ 2 ≠ 7 :=
begin
  have hn : n ≤ 2 ∨ 3 ≤ n := le_or_lt n 2,
  cases hn with hn hn,
  apply ne_of_lt,
  have : 0 ≤ n := sorry, -- soon will be built into `positivity`
  calc n ^ 2 ≤ 2 ^ 2 : by ineq_tac [hn]
  ... < 7 : by norm_num,
  apply ne_of_gt,
  calc 7 < 3 ^ 2 : by norm_num
  ... ≤ n ^ 2 : by ineq_tac [hn],
end

example {a : ℝ} (ha : a ^ 3 = 0) : a = 0 :=
begin
  have h2 : a ^ 2 = 0 ∨ a = 0,
  apply eq_zero_or_eq_zero_of_mul_eq_zero,
  calc a ^ 2 * a = a ^ 3 : by ring
  ... = 0 : ha,
  cases h2 with h2 h2,
  have h3 : a = 0 ∨ a = 0,
  apply eq_zero_or_eq_zero_of_mul_eq_zero,
  calc a * a = a ^ 2 : by ring
  ... = 0 : h2,
  cases h3 with h3 h3,
  rw h3,
  rw h3,
  rw h2,
end

example {x y : ℝ} (hxy : x ^ 2 + 5 * y = y ^ 2 + 5 * x) : x = y ∨ x + y = 5 :=
begin
  have key : (x - y) * (x + y) = (x - y) * 5,
  calc (x - y) * (x + y)
      = (x - y) * 5 + (x ^ 2 + 5 * y) - (y ^ 2 + 5 * x) : by ring
  ... = (x - y) * 5 + (y ^ 2 + 5 * x) - (y ^ 2 + 5 * x) : by rw hxy
  ... = (x - y) * 5 : by ring,
  rw mul_eq_mul_left_iff at key,
  cases key with H H,
  right,
  rw H,
  left,
  addarith [H],
end
