/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Mathport.Notation
import Math2001.Tactic.Addarith
import Math2001.Tactic.Induction
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

notation3 "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
set_option linter.unusedVariables false



/-! # Homework 6 -/


def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 4 points -/
theorem problem1 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

def b : ℕ → ℤ 
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n 

/- 4 points -/
theorem problem2 (n : ℕ) : b n = 3 ^ n - 2 ^ n := by 
  sorry

def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n 

/- 5 points -/
theorem problem3 (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  sorry

def r : ℕ → ℤ 
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n 

/- 4 points -/
theorem problem4 : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  sorry

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if n < 0 then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

/- 4 points -/
theorem problem5 (n : ℤ) : T n = n ^ 2 := by    
  sorry
