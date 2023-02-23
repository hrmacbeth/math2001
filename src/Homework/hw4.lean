/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Math2001.Library.ParityModular
import Math2001.Library.Prime
import Math2001.Tactic.Addarith
import Math2001.Tactic.ModCases
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

notation3 "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/-! # Homework 4 -/


/- 2 points -/
theorem problem1 : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry

/- 4 points -/
theorem problem2 : forall_sufficiently_large x : ℝ, x ^ 3 ≥ 7 * x ^ 2 + 12 := by
  dsimp
  sorry

/- 3 points -/
theorem problem3 {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  sorry

/- 3 points -/
theorem problem4 {x : ℤ} (hx : Int.Odd x) : Int.Odd (x ^ 3) := by
  rw [Int.odd_iff_modEq] at *
  sorry

/- 4 points -/
theorem problem5 : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  sorry

/- 5 points -/
theorem problem6 (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

/- 4 points -/
theorem problem7 : Prime 97 := by
  sorry
