/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Extra
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

/-! # Homework 5

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-5
for clearer statements and any special instructions. -/



/- 3 points -/
theorem problem1 : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  sorry

/- 4 points -/
theorem problem2 : forall_sufficiently_large x : ℝ, x ^ 3 - 2 * x ≥ 8 * x ^ 2 := by
  dsimp
  sorry

/- 4 points -/
theorem problem3 : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  sorry

/- 5 points -/
theorem problem4 : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  sorry

/- 5 points -/
theorem problem5 (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

/- 4 points -/
theorem problem6 : Prime 97 := by
  sorry
