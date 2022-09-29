/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import library.arithmetic
import tactics.inequalities


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : 
  x = 5 :=
begin
  cases h with h1 h2,
  calc x = (2 * x - y) + (y - x + 1) - 1 : by ring
  ... = 4 + 2 - 1 : by rw [h1, h2]
  ... = 5 : by ring,
end


example {p : ℚ} (hp : p ^ 2 = 9) : p ≤ 5 :=
begin
  have hp' : -3 ≤ p ∧ p ≤ 3,
  { apply abs_le_of_sq_le_sq',
    calc p ^ 2 ≤ 9 : by addarith hp
    ... = 3 ^ 2 : by norm_num1,
    norm_num1, },
  sorry,
end


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) :
  a = 9 ∧ b = 1 :=
begin
  split,
  { calc a = 4 + 5 * b : by addarith h1
    ... = -6 + 5 * (b + 2) : by ring
    ... = -6 + 5 * 3 : by rw [h2]
    ... = 9 : by ring, },
  { addarith h2, },
end


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) :
  a = 9 ∧ b = 1 :=
begin
  have hb : b = 1,
  { addarith h2 },
  split,
  { calc a = 4 + 5 * b : by addarith h1
    ... = 4 + 5 * 1 : by rw [hb]
    ... = 9 : by ring, },
  { apply hb, },
end


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 :=
begin
  have h2 : a ^ 2 = 0,
  { apply le_antisymm,
    calc a ^ 2 ≤ a ^ 2 + b ^ 2 : by ineq_tac []
    ... = 0 : by rw h1,
    ineq_tac [] },
  sorry,
end


example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 :=
begin
  sorry
end


example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
  (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) :=
begin
  sorry
end
