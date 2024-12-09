/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option quotPrecheck false


/-! # Homework 10

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-10,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autograded 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 6 * n ^ 2 ≥ 4 * n } := by
  sorry

@[autograded 4]
theorem problem1b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 6 * n ^ 2 ≥ 4 * n } := by
  sorry


/- Problem 2: prove one of these, delete the other -/

@[autograded 3]
theorem problem2a : { t : ℝ | t ^ 2 - 3 * t + 2 = 0 } = { s : ℝ | s = 2 } := by
  sorry

@[autograded 3]
theorem problem2b : { t : ℝ | t ^ 2 - 3 * t + 2 = 0 } ≠ { s : ℝ | s = 2 } := by
  sorry


/- Problem 3: prove one of these, delete the other -/

@[autograded 3]
theorem problem3a : {1, 2, 3} ∩ {2, 3, 4} ⊆ {2, 3, 6} := by
  sorry


@[autograded 3]
theorem problem3b : ¬ {1, 2, 3} ∩ {2, 3, 4} ⊆ {2, 3, 6} := by
  sorry


/- Problem 4 -/

@[autograded 4]
theorem problem4 : { r : ℤ | r ≡ 11 [ZMOD 15] }
    = { s : ℤ | s ≡ 2 [ZMOD 3] } ∩ { t : ℤ | t ≡ 1 [ZMOD 5] } := by
  sorry



/-! ### Problem 5 starts here -/


local infix:50 "∼" => fun (a b : ℤ) ↦ ∃ m n, m > 0 ∧ n > 0 ∧ a * m = b * n


/- Problem 5.1: prove one of these, delete the other -/

@[autograded 2]
theorem problem51a : Reflexive (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem51b : ¬ Reflexive (· ∼ ·) := by
  sorry


/- Problem 5.2: prove one of these, delete the other -/

@[autograded 2]
theorem problem52a : Symmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem52b : ¬ Symmetric (· ∼ ·) := by
  sorry


/- Problem 5.3: prove one of these, delete the other -/

@[autograded 2]
theorem problem53a : AntiSymmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem53b : ¬ AntiSymmetric (· ∼ ·) := by
  sorry


/- Problem 5.4: prove one of these, delete the other -/

@[autograded 2]
theorem problem54a : Transitive (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem54b : ¬ Transitive (· ∼ ·) := by
  sorry



/-! ### Problem 6 starts here -/

infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)


/- Problem 6.1: prove one of these, delete the other -/

@[autograded 2]
theorem problem61a : Reflexive (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem61b : ¬ Reflexive (· ≺ ·) := by
  sorry


/- Problem 6.2: prove one of these, delete the other -/

@[autograded 2]
theorem problem62a : Symmetric (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem62b : ¬ Symmetric (· ≺ ·) := by
  sorry


/- Problem 6.3: prove one of these, delete the other -/

@[autograded 2]
theorem problem63a : AntiSymmetric (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem63b : ¬ AntiSymmetric (· ≺ ·) := by
  sorry


/- Problem 6.4: prove one of these, delete the other -/

@[autograded 2]
theorem problem64a : Transitive (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem64b : ¬ Transitive (· ≺ ·) := by
  sorry
