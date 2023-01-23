/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.IntervalCases
import Math2001.Library.Division

def Int.Even (n : ℤ) : Prop :=
  ∃ k, n = 2 * k

def Int.Odd (n : ℤ) : Prop :=
  ∃ k, n = 2 * k + 1

theorem Int.even_or_odd (n : ℤ) : Int.Even n ∨ Int.Odd n := by
  obtain ⟨q, r, h, h', hn⟩ := n.exists_quotient_remainder 2 (by norm_num1)
  refine' exists_or.mp ⟨q, _⟩
  interval_cases r <;> simp [hn]

def Nat.Even (n : ℕ) : Prop :=
  ∃ k, n = 2 * k

def Nat.Odd (n : ℕ) : Prop :=
  ∃ k, n = 2 * k + 1

theorem Nat.even_or_odd (n : ℕ) : Nat.Even n ∨ Nat.Odd n := by
  obtain ⟨q, r, h, hn⟩ := n.exists_quotient_remainder 2 (by norm_num1)
  refine' exists_or.mp ⟨q, _⟩
  interval_cases r <;> simp [hn]
