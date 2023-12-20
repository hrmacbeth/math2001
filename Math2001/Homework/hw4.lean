/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

/-! # Homework 4

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-4
for clearer statements and any special instructions. -/

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
open Int


@[autograded 4]
theorem problem1 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
  sorry

@[autograded 4]
theorem problem2 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  sorry

@[autograded 4]
theorem problem3 {x : ℤ} (h : x ≡ 2 [ZMOD 5]) :
    (2 * x + 3) ^ 2 ≡ (2 * 2 + 3) ^ 2 [ZMOD 5] := by
  sorry

@[autograded 4]
theorem problem4 {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] :=
  sorry

@[autograded 4]
theorem problem5 : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  sorry

@[autograded 5]
theorem problem6 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  sorry
