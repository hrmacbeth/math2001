/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Tactic.Addarith
import Library.Tactic.Extra
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Rel
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option push_neg.use_distrib true
set_option linter.unusedVariables false

/-! # Homework 6

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-6
for clearer statements and any special instructions. -/



/- 4 points -/
theorem problem1 {x : ℝ} : x ^ 2 - 3 * x + 2 = 0 ↔ (x = 1 ∨ x = 2) := by
  sorry

/- 3 points -/
theorem problem2 {x : ℤ} (hx : Int.Odd x) : Int.Odd (x ^ 3) := by
  rw [Int.odd_iff_modEq] at *
  sorry

/- 4 points -/
theorem problem3 (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  sorry

/- 5 points -/
theorem problem4 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

/- 5 points -/
theorem problem5 (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  sorry

/- 4 points -/
theorem problem6 : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  sorry
