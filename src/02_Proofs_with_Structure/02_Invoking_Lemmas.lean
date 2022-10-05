/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import library.arithmetic
import tactics.addarith
import tactics.inequalities


example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 :=
begin
  apply ne_of_lt,
  calc x = (3 * x) / 3 : by ring
  ... = 2 / 3 : by rw hx
  ... < 1 : by norm_num1,
end


example {y : ℝ} : y ^ 2 + 1 ≠ 0 :=
begin
  sorry
end


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 :=
begin
  sorry
end



example (a b : ℚ) (h : a * b = 1) (h2 : 1 ≤ a) : 1 ≥ b :=
begin
  have : 0 < b,
  sorry,
  sorry,
end



lemma eq_zero_of_mul_pos_eq_zero {b : ℝ} (a : ℝ) (H1 : a * b = 0) (H2 : 0 < a) :
  b = 0 :=
begin
  sorry
end


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 :=
begin
  sorry
end


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 :=
begin
  sorry
end


lemma eq_zero_of_mul_neg_eq_zero {b : ℝ} (a : ℝ) (H1 : a * b = 0) (H2 : a < 0) :
  b = 0 :=
begin
  sorry
end


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 :=
begin
  have hx : x + 2 ≠ 0,
  sorry,
  sorry,
end

