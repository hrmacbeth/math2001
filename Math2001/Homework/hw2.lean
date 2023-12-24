/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

/-! # Homework 2

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-2
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1 {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  sorry

@[autograded 5]
theorem problem2 {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  sorry

@[autograded 2]
theorem problem3 {a b : ℝ} (h : a = 2 - b) : a + b = 2 ∨ a + b = 8 := by
  sorry

@[autograded 4]
theorem problem4 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  sorry

@[autograded 5]
theorem problem5 {x : ℤ} : 2 * x ≠ 7 := by
  sorry

@[autograded 5]
theorem problem6 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry
