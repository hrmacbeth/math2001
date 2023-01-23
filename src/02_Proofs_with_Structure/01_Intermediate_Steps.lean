/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1
  addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 : m + 3 ≤ 9
  calc
    m + 3 ≤ 2 * n - 1 := by sorry
    _ ≤ 2 * 5 - 1 := by sorry
    _ = 9 := by sorry
  sorry

example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s
  sorry
  have h4 : r ≤ 3 - s
  sorry
  calc
    r = (r + r) / 2 := by sorry
    _ ≤ (3 - s + (3 + s)) / 2 := by sorry
    _ = 3 := by sorry

example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  sorry

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  sorry

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  sorry
