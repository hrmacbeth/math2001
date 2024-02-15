/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  calc
    y ^ 2 + 1 ≥ 1 := by extra
    _ > 0 := by numbers

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra


/-! # Exercises -/


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  calc
    3 * m = 3 * (m + 1) - 3 := by ring
    _ = 3 * 5 - 3 := by rw [hm]
    _ = 12 := by ring
    _ > 6 := by numbers

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  calc
    s = 3 * s / 3 := by ring
    _ ≤ -6 / 3 := by rel [h1]
    _ = -2 := by ring

  calc
    s ≥ 2 * s / 2 := by ring
    _ ≥ -4 / 2 := by rel [h2]
    _ = -2 := by ring
