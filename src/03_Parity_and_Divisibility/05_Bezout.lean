/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.Ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  cases' hn with a ha
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  sorry

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  sorry

example {m : ℤ} (h2 : 5 ∣ m) (h1 : 8 ∣ m) : 40 ∣ m := by
  cases' h1 with a ha
  cases' h2 with b hb
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  sorry

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  sorry

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  sorry

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  sorry
