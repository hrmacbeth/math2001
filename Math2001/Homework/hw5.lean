/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

/-! # Homework 5

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-5
for clearer statements and any special instructions. -/



@[autograded 3]
theorem problem1 : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  sorry

@[autograded 4]
theorem problem2 : forall_sufficiently_large x : ℝ, x ^ 3 - 2 * x ≥ 8 * x ^ 2 := by
  dsimp
  sorry

@[autograded 4]
theorem problem3 : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  sorry

@[autograded 5]
theorem problem4 : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  sorry

@[autograded 5]
theorem problem5 (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

@[autograded 4]
theorem problem6 : Prime 97 := by
  sorry
