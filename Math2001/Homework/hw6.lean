/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-! # Homework 6

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-6,
for clearer statements and any special instructions. -/


@[autograded 4]
theorem problem1 (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  sorry

@[autograded 5]
theorem problem2 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

@[autograded 5]
theorem problem3 (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  sorry

@[autograded 3]
theorem problem4 : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  sorry

@[autograded 4]
theorem problem5 : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  sorry

@[autograded 4]
theorem problem6 {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  sorry
