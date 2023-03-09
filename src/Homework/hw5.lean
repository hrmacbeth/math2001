/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Library.Prime
import Math2001.Tactic.Addarith
import Math2001.Tactic.Induction
import Math2001.Tactic.ModCases
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

notation3 "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
set_option push_neg.use_distrib true
set_option linter.unusedVariables false

/-! # Homework 5 -/


theorem problem1 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

theorem problem2 (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  sorry

theorem problem3 {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  sorry

theorem problem4 (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by  
  sorry

theorem problem5 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2 

theorem problem6 (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  sorry
