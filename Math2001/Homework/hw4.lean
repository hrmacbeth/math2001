/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs
import AutograderLib

math2001_init

open Int

/-! # Homework 4

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-4,
for clearer statements and any special instructions. -/

@[autograded 5]
theorem problem1 (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  sorry

@[autograded 1]
theorem problem2 : (8 : ℤ) ∣ 96 := by
  sorry

@[autograded 2]
theorem problem3 : ¬(8 : ℤ) ∣ -55 := by
  sorry

@[autograded 4]
theorem problem4 {a b c : ℤ} (hab : a ^ 3 ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 6 ∣ c := by
  sorry

@[autograded 1]
theorem problem5 : 31 ≡ 13 [ZMOD 3] := by
  sorry

@[autograded 2]
theorem problem6 : ¬ 51 ≡ 62 [ZMOD 5] := by
  sorry

@[autograded 5]
theorem problem7 (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  sorry

@[autograded 5]
theorem problem8 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  sorry
