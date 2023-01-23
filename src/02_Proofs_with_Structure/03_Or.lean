/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Library.Arithmetic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Rel


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  cases' h with hx hy
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring    
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn : n ≤ 1 ∨ 2 ≤ n
  apply le_or_lt
  cases' hn with hn hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by ineq_rel [hn]
    _ < 2 := by norm_num1
  sorry

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by norm_num1


example {a b : ℝ} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have ha : a < 0 ∨ a = 0 ∨ 0 < a
  apply lt_trichotomy
  cases' ha with ha ha
  right
  apply eq_zero_of_mul_neg_eq_zero a
  apply h
  apply ha
  cases' ha with ha ha
  left
  apply ha
  sorry

example {a b : ℝ} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0
  cases' ha with ha ha
  right
  apply eq_zero_of_mul_neg_eq_zero a h ha
  cases' ha with ha ha
  left
  apply ha
  sorry

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have hx' : x - 1 = 0 ∨ x - 2 = 0
  apply eq_zero_or_eq_zero_of_mul_eq_zero
  sorry
  sorry

example {a : ℝ} (ha : a ^ 2 = 0) : a = 0 := by
  sorry

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 : n ≤ 0 ∨ 1 ≤ n := le_or_lt n 0
  cases' hn0 with hn0 hn0
  · have : 0 ≤ -n
    addarith [hn0]
    have hn : -n ≤ 1 ∨ 2 ≤ -n := le_or_lt (-n) 1
    cases' hn with hn hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ (1:ℤ) ^ 2 := by ineq_rel [hn]
        _ < 2 := by norm_num1
    · apply ne_of_gt
      calc
        2 < 2 ^ 2 := by norm_num1
        _ ≤ (-n) ^ 2 := by ineq_rel [hn]
        _ = n ^ 2 := by ring
  · have hn : n ≤ 1 ∨ 2 ≤ n := le_or_lt n 1
    cases' hn with hn hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ (1:ℤ) ^ 2 := by ineq_rel [hn]
        _ < (2:ℤ) := by norm_num1
    · apply ne_of_gt
      calc
        2 < 2 ^ 2 := by norm_num1
        _ ≤ n ^ 2 := by ineq_rel [hn]


example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  sorry

example {n : ℕ} : n ^ 2 ≠ 7 := by
  sorry

example {a : ℝ} (ha : a ^ 3 = 0) : a = 0 := by
  sorry
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  sorry

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry

example {x y : ℝ} (hxy : x ^ 2 + 5 * y = y ^ 2 + 5 * x) : x = y ∨ x + y = 5 := by
  sorry

example {a b c : ℚ} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have h1 : a * (b - c) = 0
  sorry
  have h2 : b - c = 0
  sorry
  sorry
