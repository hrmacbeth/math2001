/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Define
import Math2001.Tactic.ExistsDelaborator
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option linter.unusedVariables false
set_option pp.unicode.fun true
set_option push_neg.use_distrib true
open Function
notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)


/-! # Homework 8 -/


theorem problem1 : Surjective (fun ((a, b) : ℚ × ℕ) ↦ a ^ b) := by
  sorry

theorem problem2 : ¬ Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  sorry

theorem problem3a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry

theorem problem3b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry


theorem problem4a : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } = { s : ℝ | s = 4 } := by
  sorry

theorem problem4b : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } ≠ { s : ℝ | s = 4 } := by
  sorry

theorem problem5a : { k : ℤ | 7 ∣ 9 * k } = { l : ℤ | 7 ∣ l } := by
  sorry

theorem problem5b : { k : ℤ | 7 ∣ 9 * k } ≠ { l : ℤ | 7 ∣ l } := by
  sorry


theorem problem6a : {1, 2, 3} = {1, 2} := by
  sorry

theorem problem6b : {1, 2, 3} ≠ {1, 2} := by
  sorry
