/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Define
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Take

set_option linter.unusedVariables false
set_option pp.unicode.fun true
set_option push_neg.use_distrib true
open Function
notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)


/-! # Homework 8 -/


/- 4 points -/
theorem problem1 : Surjective (fun ((a, b) : ℚ × ℕ) ↦ a ^ b) := by
  sorry

/- 4 points -/
theorem problem2 : ¬ Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  sorry

/- 4 points -/
theorem problem3a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry

/- 4 points -/
theorem problem3b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry


/- 4 points -/
theorem problem4a : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } = { s : ℝ | s = 4 } := by
  sorry

/- 4 points -/
theorem problem4b : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } ≠ { s : ℝ | s = 4 } := by
  sorry

/- 5 points -/
theorem problem5a : { k : ℤ | 7 ∣ 9 * k } = { l : ℤ | 7 ∣ l } := by
  sorry

/- 5 points -/
theorem problem5b : { k : ℤ | 7 ∣ 9 * k } ≠ { l : ℤ | 7 ∣ l } := by
  sorry


/- 4 points -/
theorem problem6a : {1, 2, 3} = {1, 2} := by
  sorry

/- 4 points -/
theorem problem6b : {1, 2, 3} ≠ {1, 2} := by
  sorry
