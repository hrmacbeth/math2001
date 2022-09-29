/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import library.arithmetic
import tactics.inequalities


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 :=
begin
  cases h with b hb,
  calc a = b ^ 2 + 1 : hb
  ... > 0 : by ineq_tac [],
end


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 :=
begin
  cases h with x hxt,
  have H : x ≤ 0 ∨ 0 < x := le_or_gt x 0,
  cases H with hx hx,
  { apply ne_of_gt,
    apply pos_of_mul_neg_right hxt hx, },
  sorry,
end


example : ∃ n : ℤ, 12 * n = 84 :=
begin
  use 7,
  norm_num1,
end


example (x : ℝ) : ∃ y : ℝ, y > x :=
begin
  use x + 1,
  ineq_tac [],
end


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 :=
begin
  sorry,
end


example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 :=
begin
  sorry,
end


example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q :=
begin
  sorry,
end


example : ∃ a b c d : ℕ, a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d :=
begin
  use [1, 12, 9, 10],
  split,
  norm_num1,
  split,
  norm_num1,
  split,
  norm_num1,
  norm_num1,
end


example : ∃ t : ℚ, t ^ 2 = 1.69 :=
begin
  sorry,
end


example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 :=
begin
  sorry,
end


example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 :=
begin
  sorry,
end


example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 :=
begin
  sorry,
end


example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x :=
begin
  sorry,
end


example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 :=
begin
  sorry,
end


example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 :=
begin
  sorry,
end


example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) 
  (ha' : 0 ≤ a) (hb' : 0 ≤ b) (hc' : 0 ≤ c) :
  ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y :=
begin
  sorry,
end
