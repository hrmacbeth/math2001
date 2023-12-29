/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
set_option push_neg.use_distrib true
set_option pp.funBinderTypes true

/-! # Homework 6

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-6
for clearer statements and any special instructions. -/



@[autograded 4]
theorem problem1 {x : ℝ} : x ^ 2 - 3 * x + 2 = 0 ↔ (x = 1 ∨ x = 2) := by
  sorry

@[autograded 3]
theorem problem2 {x : ℤ} (hx : Int.Odd x) : Int.Odd (x ^ 3) := by
  rw [Int.odd_iff_modEq] at *
  sorry

@[autograded 4]
theorem problem3 (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  sorry

@[autograded 5]
theorem problem4 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

@[autograded 5]
theorem problem5 (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  sorry

@[autograded 4]
theorem problem6 : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  sorry
