/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import AutograderLib

math2001_init

open Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/

@[autograded 2]
theorem problem1 {a b : ℚ} (h : a = 3 - b) : a + b = 3 ∨ a + b = 4 := by
  sorry

@[autograded 5]
theorem problem2 {t : ℚ} (h : t ^ 2 + t - 6 = 0) : t = 2 ∨ t = -3 := by
  sorry

@[autograded 3]
theorem problem3 : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  sorry

@[autograded 5]
theorem problem4 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

@[autograded 5]
theorem problem5 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

@[autograded 5]
theorem problem6 (n : ℕ) : ∃ m ≥ n, Odd m := by
  sorry
