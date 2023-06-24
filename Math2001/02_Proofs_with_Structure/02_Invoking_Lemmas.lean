/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Numbers
import Library.Tactic.Extra

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  sorry

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  sorry

example (x y : ℚ) (h : x * y = 1) (h2 : 1 ≤ x) : 1 ≥ y := by
  have : 0 < y
  sorry
  sorry

example {b : ℝ} (a : ℝ) (H1 : a * b = 0) (H2 : 0 < a) : b = 0 := by
  sorry

example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  sorry

example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  sorry

example {b : ℝ} (a : ℝ) (H1 : a * b = 0) (H2 : a < 0) : b = 0 := by
  sorry

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have hx : x + 2 ≠ 0
  sorry
  sorry
