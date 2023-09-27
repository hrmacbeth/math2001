/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Tactic.Addarith
import Library.Tactic.Extra
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Use

/-! # Homework 4 

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-4
for clearer statements and any special instructions. -/

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
open Int


/- 4 points -/
theorem problem1 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
  sorry

/- 4 points -/
theorem problem2 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  sorry

/- 4 points -/
theorem problem3 {x : ℤ} (h : x ≡ 2 [ZMOD 5]) :
    (2 * x + 3) ^ 2 ≡ (2 * 2 + 3) ^ 2 [ZMOD 5] := by
  sorry

/- 4 points -/
theorem problem4 {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] :=
  sorry

/- 4 points -/
theorem problem5 : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  sorry

/- 5 points -/
theorem problem6 {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  sorry
