/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.addarith
import tactics.inequalities
import tactics.positivity
import library.arithmetic2


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 :=
begin
  cases h with hx hy,
  calc x * y + x = 1 * y + 1 : by rw [hx]
  ... = y + 1 : by ring,
  calc x * y + x = x * -1 + x : by rw [hy]
  ... = -1 + 1 : by ring
  ... = y + 1 : by rw [hy],
end


example {n : ℕ} : n ^ 2 ≠ 2 :=
begin
  have hn : n ≤ 1 ∨ 2 ≤ n,
  apply le_or_lt,
  cases hn with hn hn,
  apply ne_of_lt,
  calc n ^ 2 ≤ 1 ^ 2 : by ineq_tac [hn]
  ... < 2 : by norm_num1,
  sorry,
end


example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 :=
begin
  right,
  calc x = ((2 * x + 1) - 1) / 2 : by ring
  ... = (5 - 1) / 2 : by rw hx
  ... = 2 : by norm_num1,
end


example {a b : ℝ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin
  have ha : a < 0 ∨ a = 0 ∨ 0 < a,
  apply lt_trichotomy,
  cases ha with ha ha,
  right,
  apply eq_zero_of_mul_neg_eq_zero a,
  apply h,
  apply ha,
  cases ha with ha ha,
  left,
  apply ha,
  sorry,
end


example {a b : ℝ} (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin
  have ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0,
  cases ha with ha ha,
  right,
  apply eq_zero_of_mul_neg_eq_zero a h ha,
  cases ha with ha ha,
  left,
  apply ha,
  sorry,
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
      ... < 2 : by norm_num1 },
    { apply ne_of_gt,
      calc 2 < 2 ^ 2 : by norm_num1
      ... ≤ (-n) ^ 2 : by ineq_tac [hn]
      ... = n ^ 2 : by ring } },
  { have hn : n ≤ 1 ∨ 2 ≤ n := le_or_lt n 1,
    cases hn with hn hn,
    { apply ne_of_lt,
      calc n ^ 2 ≤ 1 ^ 2 : by ineq_tac [hn]
      ... < 2 : by norm_num1 },
    { apply ne_of_gt,
      calc 2 < 2 ^ 2 : by norm_num1
      ... ≤ n ^ 2 : by ineq_tac [hn] } },
end


example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 :=
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

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 :=
begin
  sorry,
end


example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 :=
begin
  sorry,
end


example {x y : ℝ} (hxy : x ^ 2 + 5 * y = y ^ 2 + 5 * x) : x = y ∨ x + y = 5 :=
begin
  sorry,
end


example {a b c : ℚ} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
begin
  have h1  : a * (b - c) = 0,
  sorry,
  have h2 : b - c = 0,
  sorry,
  sorry,
end
