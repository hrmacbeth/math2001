/- Copyright (c) Heather Macbeth, 2024.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

macro_rules | `(tactic| gcongr_discharger) => `(tactic| numbers)
math2001_init

namespace Nat

/-! # Homework 8

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-8,
for clearer statements and any special instructions. -/


def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

@[autograded 4]
theorem problem1 (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

@[autograded 4]
theorem problem2 (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  sorry


def a : ℕ → ℤ
  | 0 => 4
  | n + 1 => 3 * a n - 5

@[autograded 4]
theorem problem3 : forall_sufficiently_large (n : ℕ), a n ≥ 10 * 2 ^ n := by
  sorry


def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

@[autograded 4]
theorem problem4 (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by
  sorry


def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

@[autograded 4]
theorem problem5 (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  sorry


@[autograded 5]
theorem problem6 (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  sorry
