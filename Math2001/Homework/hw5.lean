/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Take

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option push_neg.use_distrib true
set_option linter.unusedVariables false

/-! # Homework 5 -/


/- 4 points -/
theorem problem1 (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

/- 5 points -/
theorem problem2 (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  sorry

/- 4 points -/
theorem problem3 {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  sorry

/- 4 points -/
theorem problem4 (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by  
  sorry

/- 4 points -/
theorem problem5 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2 

/- 4 points -/
theorem problem6 (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  sorry
