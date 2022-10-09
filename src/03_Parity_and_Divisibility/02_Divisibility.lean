/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import library.arithmetic
import library.division
import tactics.inequalities

local attribute [-norm_num] norm_num.eval_nat_int_ext


example : (11:ℕ) ∣ 88 :=
begin
  dsimp [(∣)],
  use 8,
  norm_num1,
end


example : (-2:ℤ) ∣ 6 :=
begin
  sorry,
end


example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b :=
begin
  cases hab with k hk,
  use k * (a * k + 2),
  calc b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) : by rw [hk]
  ... = a * (k * (a * k + 2)) : by ring 
end


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c :=
begin
  sorry,
end 



example {x y z : ℕ} (h : (x * y) ∣ z) : x ∣ z :=
begin
  sorry,
end


example : ¬ ((5:ℤ) ∣ 12) :=
begin
  apply int.not_dvd_of_exists_lt_and_lt,
  norm_num,
  use 2,
  split,
  norm_num,
  norm_num,
end


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b :=
begin
  cases hab with k hk,
  have H : 1 ≤ k,
  apply pos_of_mul_pos_right' a,
  calc 0 < b : hb
  ... = a * k : hk,
  ineq_tac [],
  calc a = a * 1 : by ring
  ... ≤ a * k : by ineq_tac [H]
  ... = b : by rw hk,
end


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a :=
begin
  sorry,
end


example (t : ℤ) : t ∣ 0 :=
begin
  sorry,
end


example : ¬ ((3:ℤ) ∣ -10) :=
begin
  sorry,
end


example {a b : ℤ} (hab : a ∣ b) : a ∣ (3 * b ^ 3 - b ^ 2 + 5 * b) :=
begin
  sorry,
end


example {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c :=
begin
  sorry,
end


example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 :=
begin
  sorry,
end



example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b :=
begin
  sorry,
end


example (a : ℕ) (h : a ^ 2 ∣ a) : a = 0 ∨ a = 1 :=
begin
  have ha : 0 ≤ a := by ineq_tac [],
  cases eq_or_lt_of_le ha with ha ha,
  { sorry },
  have H1 : a ^ 2 = a,
  { sorry },
  have H2 : a = 1 ∨ a = 0,
  { sorry },
  sorry,
end
