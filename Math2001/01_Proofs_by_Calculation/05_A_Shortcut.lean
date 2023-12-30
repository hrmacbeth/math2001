/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.5: A shortcut -/

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by addarith [h1]

example {a b : ℤ} (ha : a - 2 * b = 1) : a = 2 * b + 1 := by addarith [ha]

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 :=
  calc
    x + y ^ 2 = x - 7 := by addarith [hy]
    _ = -5 := by addarith [hx]


example {s t : ℝ} (h : t = 4 - s * t) : t + s * t > 0 := by addarith [h]

example {m n : ℝ} (h1 : m ≤ 8 - n) : 10 > m + n := by addarith [h1]


-- Check that `addarith` can't verify this deduction!
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := sorry
