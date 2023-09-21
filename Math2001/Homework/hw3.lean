/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

/-! # Homework 3 

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-3
for clearer statements and any special instructions. -/

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat


/- 4 points -/
theorem problem1 : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  sorry

/- 5 points -/
theorem problem2 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  sorry

namespace Int

/- 5 points -/
theorem problem3 {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

/- 6 points -/
theorem problem4 (n : ℤ) : Odd (5 * n ^ 2 + 3 * n + 7) := by
  sorry

/- 2 points -/
theorem problem5 : (3 : ℤ) ∣ -9 := by
  sorry

/- 3 points -/
theorem problem6 : ¬(3 : ℤ) ∣ -10 := by
  sorry
