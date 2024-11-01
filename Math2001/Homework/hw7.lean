/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init


/-! # Homework 7

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-7,
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  sorry

@[autograded 3]
theorem problem2 : ¬ (∀ x : ℚ, 2 * x ^ 2 ≥ x) := by
  push_neg
  sorry

@[autograded 4]
theorem problem3 (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  sorry

@[autograded 4]
theorem problem4 (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  sorry

@[autograded 5]
theorem problem5 {a : ℝ} (ha : -1 ≤ a) : ¬ ∃ n : ℕ, (1 + a) ^ n < 1 + n * a := by
  push_neg
  sorry

@[autograded 4]
theorem problem6 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry
