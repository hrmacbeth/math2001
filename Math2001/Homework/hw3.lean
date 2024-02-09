/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import AutograderLib

math2001_init

open Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/


@[autograded 3]
theorem problem1 : ∃ x : ℚ, x < 0 ∧ x ^ 2 < 1 := by
  sorry

@[autograded 5]
theorem problem2 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

@[autograded 4]
theorem problem3 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

@[autograded 5]
theorem problem4 (n : ℕ) : ∃ m ≥ n, Odd m := by
  sorry

@[autograded 2]
theorem problem5 : (4 : ℤ) ∣ -12 := by
  sorry

@[autograded 2]
theorem problem6 : ¬(3 : ℤ) ∣ -11 := by
  sorry

@[autograded 4]
theorem problem7 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
  sorry
