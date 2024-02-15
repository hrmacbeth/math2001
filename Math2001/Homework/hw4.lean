/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init


/-! # Homework 4

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-4,
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  sorry

@[autograded 4]
theorem problem2 {t : ℤ} (h : t ≡ 2 [ZMOD 4]) :
    3 * (t ^ 2 + t - 8) ≡ 3 * (2 ^ 2 + 2 - 8) [ZMOD 4] := by
  sorry

@[autograded 4]
theorem problem3 {a : ℤ} (ha : a ≡ 3 [ZMOD 5]) :
    a ^ 3 + 4 * a ^ 2 + 3 ≡ 1 [ZMOD 5] := by
  sorry

@[autograded 4]
theorem problem4 : ∃ k : ℤ, k > 50 ∧ k ≡ 2 [ZMOD 5] ∧ 5 * k ≡ 6 [ZMOD 8] := by
  sorry

@[autograded 5]
theorem problem5 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  sorry

@[autograded 4]
theorem problem6 {n : ℤ} (h1 : 5 ∣ n) (h2 : 12 ∣ n) : 60 ∣ n := by
  sorry
