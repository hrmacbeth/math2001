/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactic.interval_cases
import tactics.inequalities


example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
calc a ≤ 1 ^ 2 - 2 * 1 : by apply h
... = -1 : by norm_num1


example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 :=
begin
  sorry
end


example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b :=
begin
  sorry
end


example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
  (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
  a = b :=
begin
  apply le_antisymm,
  { apply hb2,
    apply ha1, },
  sorry
end


example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x :=
begin
  use -1,
  intros x,
  calc -1 ≤ -1 + (x - 1) ^ 2 : by ineq_tac []
  ... = x ^ 2 - 2 * x : by ring,
end


example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c :=
begin
  sorry,
end


notation `forall_sufficiently_large` binders `, ` r:(scoped P, ∃ C, ∀ x ≥ C, P x) := r

example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 :=
begin
  use 5,
  intros n hn,
  calc n ^ 3 = n * n ^ 2 : by ring
  ... ≥ 5 * n ^ 2 : by ineq_tac [hn]
  ... = 4 * n ^ 2 + n ^ 2 : by ring
  ... ≥ 4 * n ^ 2 + 5 ^ 2 : by ineq_tac [hn]
  ... = 4 * n ^ 2 + 7 + 18 : by ring
  ... ≥ 4 * n ^ 2 + 7 : by ineq_tac [],
end


def prime (p : ℕ) : Prop := 2 ≤ p ∧ ∀ (m : ℕ) (hm : m ∣ p), m = 1 ∨ m = p


example : prime 2 :=
begin
  split,
  { norm_num1, },
  intros m hmp,
  have hp : 0 < 2 := by norm_num,
  have hmp_le : m ≤ 2 := nat.le_of_dvd hp hmp,
  have h1m : 1 ≤ m := nat.pos_of_dvd_of_pos hmp hp,
  interval_cases m,
  { left,
    norm_num1, },
  { right,
    norm_num1, },
end


example {a : ℚ} (h : ∀ b : ℚ, a ≥ - 3 + 4 * b - b ^ 2) : a ≥ 1 :=
sorry

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n :=
begin
  sorry,
end


example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m :=
begin
  sorry,
end


example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 :=
begin
  sorry,
end

