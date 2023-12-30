/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  sorry

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  sorry

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  sorry

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  sorry

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  sorry

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  sorry

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  sorry

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  sorry

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  sorry

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  sorry

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  sorry

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry

example {n : ℕ} : n ^ 2 ≠ 7 := by
  sorry

example {x : ℤ} : 2 * x ≠ 3 := by
  sorry

example {t : ℤ} : 5 * t ≠ 18 := by
  sorry

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry
