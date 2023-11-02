/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Mathport.Notation
import Mathlib.Tactic.GCongr
import Library.Tactic.Addarith
import Library.Tactic.Induction
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
set_option linter.unusedVariables false



/-! # Homework 7

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-7
for clearer statements and any special instructions. -/



/- 4 points -/
theorem problem1 (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry

/- 4 points -/
theorem problem2 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

/- 4 points -/
theorem problem3 (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  sorry

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 4 points -/
theorem problem4 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

/- 4 points -/
theorem problem5 (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  sorry

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

/- 5 points -/
theorem problem6 : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  sorry
