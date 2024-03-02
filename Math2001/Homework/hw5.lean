/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

-- BOTH:
math2001_init

/-! # Homework 5

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-5,
for clearer statements and any special instructions. -/

@[autograded 4]
theorem problem1 : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + c < b := by
  sorry

@[autograded 4]
theorem problem2 : forall_sufficiently_large x : ℝ, x ^ 3 - 3 * x ≥ 12 * x ^ 2 := by
  dsimp
  sorry

@[autograded 3]
theorem problem3 (x : ℝ) : 3 * x + 1 = 10 ↔ x = 3 := by
  sorry

@[autograded 6]
theorem problem4 (n : ℤ) : n ^ 2 + n + 3 ≡ 0 [ZMOD 5] ↔ n ≡ 1 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  sorry

@[autograded 4]
theorem problem5 : ¬ (∃ t : ℝ, 2 * t ≤ 8 ∧ t ≥ 5) := by
  sorry

@[autograded 4]
theorem problem6 : ¬ (∃ a : ℝ, ∀ b : ℝ, a ≤ b) := by
  sorry
