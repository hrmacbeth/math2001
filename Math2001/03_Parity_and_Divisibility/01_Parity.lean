/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Int.Odd (7 : ℤ) := by
  dsimp [Int.Odd]
  use 3
  numbers


example : Int.Odd (-3 : ℤ) := by
  sorry

example {n : ℤ} (hn : Int.Odd n) : Int.Odd (3 * n + 2) := by
  dsimp [Int.Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Int.Odd n) : Int.Odd (7 * n - 4) := by
  sorry

example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x * y + 2 * y) := by
  sorry

example {m : ℤ} (hm : Int.Odd m) : Int.Even (3 * m - 5) := by
  sorry

example {n : ℤ} (hn : Int.Even n) : Int.Odd (n ^ 2 + 2 * n - 5) := by
  sorry

example (n : ℤ) : Int.Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd_lib n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Int.Odd (-9 : ℤ) := by
  sorry

example : Int.Even (26 : ℤ) := by
  sorry

example {m n : ℤ} (hm : Int.Odd m) (hn : Int.Even n) : Int.Odd (n + m) := by
  sorry

example {p q : ℤ} (hp : Int.Odd p) (hq : Int.Even q) : Int.Odd (p - q - 4) := by
  sorry

example {a b : ℤ} (ha : Int.Even a) (hb : Int.Odd b) : Int.Even (3 * a + b - 3) := by
  sorry

example {r s : ℤ} (hr : Int.Odd r) (hs : Int.Odd s) : Int.Even (3 * r - 5 * s) := by
  sorry

example {x : ℤ} (hx : Int.Odd x) : Int.Odd (x ^ 3) := by
  sorry

example {n : ℤ} (hn : Int.Odd n) : Int.Even (n ^ 2 - 3 * n + 2) := by
  sorry

example {a : ℤ} (ha : Int.Odd a) : Int.Odd (a ^ 2 + 2 * a - 4) := by
  sorry

example {p : ℤ} (hp : Int.Odd p) : Int.Odd (p ^ 2 + 3 * p - 5) := by
  sorry

example {x y : ℤ} (hx : Int.Odd x) (hy : Int.Odd y) : Int.Odd (x * y) := by
  sorry

example (n : ℤ) : Int.Odd (3 * n ^ 2 + 3 * n - 1) := by
  sorry

example (n : ℤ) : ∃ m ≥ n, Int.Odd m := by
  sorry
example (a b c : ℤ) : Int.Even (a - b) ∨ Int.Even (a + c) ∨ Int.Even (b - c) := by
  sorry
