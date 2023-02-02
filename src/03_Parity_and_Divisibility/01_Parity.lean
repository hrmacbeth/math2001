/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Math2001.Library.Parity
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  take 3
  numbers


example : Odd (-3 : ℤ) := by
  sorry

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  take 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  sorry

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  take a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  sorry

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  sorry

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  sorry

example (n : ℤ) : Even (n ^ 2 + 3 * n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    take 2 * x ^ 2 + 3 * x + 2
    calc
      n ^ 2 + 3 * n + 4 = (2 * x) ^ 2 + 3 * (2 * x) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    take 2 * x ^ 2 + 5 * x + 4
    calc
      n ^ 2 + 3 * n + 4 = (2 * x + 1) ^ 2 + 3 * (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 5 * x + 4) := by ring


example : Odd (-9 : ℤ) := by
  sorry

example : Even (26 : ℤ) := by
  sorry

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  sorry

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  sorry

example (n : ℤ) : Odd (5 * n ^ 2 + 3 * n + 7) := by
  sorry

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  sorry
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  sorry
