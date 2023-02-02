/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

/-! # Homework 2 -/


/- 5 points -/
theorem problem1 {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry

/- 5 points -/
theorem problem2 {a : ℝ} (ha : a ^ 3 = 0) : a = 0 := by
  sorry

/- 5 points -/
theorem problem3 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  sorry

/- 3 points -/
theorem problem4 : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  sorry

/- 3 points -/
theorem problem5 : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry

/- 4 points -/
theorem problem6 {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  sorry
