/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init


/-! # Homework 7

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-7,
for clearer statements and any special instructions. -/



@[autograded 4]
theorem problem1 (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry

@[autograded 4]
theorem problem2 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

@[autograded 4]
theorem problem3 (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  sorry

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

@[autograded 4]
theorem problem4 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

@[autograded 4]
theorem problem5 (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  sorry

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

@[autograded 5]
theorem problem6 : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  sorry
