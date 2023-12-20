/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq
import AutograderLib

set_option quotPrecheck false
set_option push_neg.use_distrib true
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
open Function


/-! # Homework 10

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-10
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1a : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry

@[autograded 4]
theorem problem1b : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry


@[autograded 4]
theorem problem2a : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } = { s : ℝ | s = 4 } := by
  sorry

@[autograded 4]
theorem problem2b : { t : ℝ | t ^ 2 - 5 * t + 4 = 0 } ≠ { s : ℝ | s = 4 } := by
  sorry

@[autograded 4]
theorem problem3a : {1, 2, 3} = {1, 2} := by
  sorry

@[autograded 4]
theorem problem3b : {1, 2, 3} ≠ {1, 2} := by
  sorry

@[autograded 4]
theorem problem4 : { r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ { s : ℤ | s ≡ 1 [ZMOD 2] } ∩ { t : ℤ | t ≡ 2 [ZMOD 5] } := by
  sorry

local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

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

@[autograded 3]
theorem problem53a : AntiSymmetric (· ∼ ·) := by
  sorry

@[autograded 3]
theorem problem53b : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem54a : Transitive (· ∼ ·) := by
  sorry

@[autograded 2]
theorem problem54b : ¬ Transitive (· ∼ ·) := by
  sorry
