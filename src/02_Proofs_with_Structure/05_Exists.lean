/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  cases' h with b hb
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by rel


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  cases' h with x hxt
  have H : x ≤ 0 ∨ 0 < x := le_or_gt x 0
  cases' H with hx hx
  · apply ne_of_gt
    apply pos_of_mul_neg_right hxt hx
  · sorry

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  rel


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  sorry

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  sorry

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  sorry

example : ∃ a b c d : ℕ, a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  sorry
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  sorry

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  sorry

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b)
    (ha' : 0 ≤ a) (hb' : 0 ≤ b) (hc' : 0 ≤ c) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
