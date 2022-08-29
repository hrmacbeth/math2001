/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import library.arithmetic
import tactics.inequalities

example {y : ℝ} : y ^ 2 + 1 ≠ 0 :=
begin
  apply ne_of_gt,
  ineq_tac [],
end

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 :=
begin
  apply le_antisymm,
  calc a ^ 2 = a ^ 2 + 0 : by ring
  ... ≤ a ^ 2 + b ^ 2 : by ineq_tac []
  ... = 0 : h1,
  ineq_tac [],
end


example (a b : ℚ) (h : a * b = 1) (h2 : 1 ≤ a) : 1 ≥ b :=
begin
  have : 0 < b,
  apply pos_of_mul_pos_right' a,
  addarith [h],
  ineq_tac [],
  calc 1 = a * b : by rw h
  ... ≥ 1 * b : by ineq_tac [h2]
  ... = b : by ring,
end


lemma eq_zero_of_mul_pos_eq_zero {b : ℝ} (a : ℝ) (h : a * b = 0) (ha : 0 < a) :
  b = 0 :=
begin
  apply le_antisymm,
  apply nonpos_of_mul_nonpos_right' a,
  addarith [h],
  apply ha,
  apply nonneg_of_mul_nonneg_right' a,
  addarith [h],
  apply ha,
end

example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 :=
begin
  apply ne_of_gt,
  calc 6 < 3 * 5 - 3 : by norm_num
  ... = 3 * (m + 1) - 3 : by rw [hm]
  ... = 3 * m : by ring,
end

example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 :=
begin
  apply le_of_pow_le_pow 2,
  ineq_tac [],
  norm_num,
  calc a ^ 2 = b ^ 2 + 1 : by rw h1
  ... ≥ 0 + 1 : by ineq_tac []
  ... = 1 ^ 2 : by ring,
end

lemma eq_zero_of_mul_neg_eq_zero {b : ℝ} (a : ℝ) (h : a * b = 0) (ha : a < 0) :
  b = 0 :=
begin
  apply le_antisymm,
  apply nonpos_of_mul_nonneg_right' a,
  addarith [h],
  apply ha,
  apply nonneg_of_mul_nonpos_right' a,
  addarith [h],
  apply ha,
end

