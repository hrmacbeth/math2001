/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init

/-! # Homework 5

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-5,
for clearer statements and any special instructions. -/

@[autograded 2]
theorem problem1 : ∃ k : ℤ, k > 10 ∧ 3 * k ≡ 2 [ZMOD 5] ∧ k ∣ 72 := by
  sorry

@[autograded 3]
theorem problem2 {a : ℤ} (ha : a ≡ 4 [ZMOD 5]) :
    a ^ 3 + 2 * a ^ 2 + 3 ≡ 4 [ZMOD 5] := by
  sorry

@[autograded 5]
theorem problem3 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  sorry

@[autograded 3]
theorem problem4 {a : ℚ} (h : ∀ b : ℚ, a + b ^ 2 ≥ 0) : a ≥ 0 := by
  sorry

@[autograded 5]
theorem problem5 (n : ℕ) (h : ∀ a : ℕ, 6 ≤ a → a ≤ 10 → a ∣ n) :
    ∀ b : ℕ, 1 ≤ b → b ≤ 5 → b ∣ n := by
  sorry

@[autograded 3]
theorem problem6 : ∃ a : ℝ, ∀ b : ℝ, a ≤ b ^ 2 := by
  sorry

@[autograded 4]
theorem problem7 : forall_sufficiently_large x : ℝ, x ^ 3 - 5 * x ≥ 11 * x ^ 2 := by
  dsimp
  sorry
