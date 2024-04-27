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


@[autograded 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 8 * n ^ 2 ≥ 2 * n } := by
  sorry

@[autograded 4]
theorem problem1b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 8 * n ^ 2 ≥ 2 * n } := by
  sorry


@[autograded 4]
theorem problem2a : { t : ℝ | t ^ 2 - 5 * t + 6 = 0 } = { s : ℝ | s = 2 } := by
  sorry

@[autograded 4]
theorem problem2b : { t : ℝ | t ^ 2 - 5 * t + 6 = 0 } ≠ { s : ℝ | s = 2 } := by
  sorry


@[autograded 4]
theorem problem3a : {1, 2, 3} = {1, 2} := by
  sorry

@[autograded 4]
theorem problem3b : {1, 2, 3} ≠ {1, 2} := by
  sorry


@[autograded 4]
theorem problem4 : { r : ℤ | r ≡ 8 [ZMOD 10] }
    ⊆ { s : ℤ | s ≡ 0 [ZMOD 2] } ∩ { t : ℤ | t ≡ 3 [ZMOD 5] } := by
  sorry


/-! ### Problem 5 starts here -/

infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

@[autograded 2]
theorem problem51a : Reflexive (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem51b : ¬ Reflexive (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem52a : Symmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem52b : ¬ Symmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem53a : AntiSymmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem53b : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem54a : Transitive (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem54b : ¬ Transitive (· ∼ ·) := by
  sorry


/-! ### Problem 6 starts here -/

infix:50 "≺" => fun ((x1, y1) : ℝ × ℝ) (x2, y2) ↦ (x1 ≤ x2 ∧ y1 ≤ y2)

@[autograded 2]
theorem problem61a : Reflexive (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem61b : ¬ Reflexive (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem62a : Symmetric (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem62b : ¬ Symmetric (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem63a : AntiSymmetric (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem63b : ¬ AntiSymmetric (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem64a : Transitive (· ≺ ·) := by
  sorry

@[autograded 2]
theorem problem64b : ¬ Transitive (· ≺ ·) := by
  sorry
