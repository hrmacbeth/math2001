/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use (-2)
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨p, hp⟩ := hn
  use 7 * p + 1
  calc
    7 * n - 4 = 7 * (2 * p + 1) - 4 := by rw [hp]
    _ = 2 * (7 * p + 1) + 1 := by ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc
    x + y + 1 = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + 3 * b + a + 1
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + 3 * b + a + 1) + 1 := by ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  use 3 * t - 1
  calc
    3 * m - 5 = 3 * (2 * t + 1) - 5 := by rw [ht]
    _ = 2 * (3 * t - 1) := by ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨t, ht⟩ := hn
  use 2 * t ^ 2 + 2 * t - 3
  calc
    n ^ 2 + 2 * n - 5 = (2 * t) ^ 2 + 2 * (2 * t) - 5 := by rw [ht]
    _ = 2 * (2 * t ^ 2 + 2 * t - 3) + 1 := by ring

example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
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


example : Odd (-9 : ℤ) := by
  use -5
  numbers

example : Even (26 : ℤ) := by
  use 13
  numbers

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, ht⟩ := hn
  use s + t
  calc
    n + m = 2 * t + (2 * s  + 1) := by rw [hs, ht]
    _ = 2 * (s + t) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨t, ht⟩ := hq
  use s - t - 2
  calc
    p - q - 4 = 2 * s + 1 - (2 * t) - 4 := by rw [hs, ht]
    _ = 2 * (s - t - 2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  sorry

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  sorry

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  sorry

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  sorry

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  sorry

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  sorry

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  sorry

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  dsimp [Odd] at *
  obtain hn := Int.even_or_odd n
  obtain hn1 | hn2 := hn
  use n + 1
  constructor
  · extra
  ·
    obtain ⟨s, hs⟩ := hn1
    use s
    calc
      n + 1 = 2 * s + 1 := by rw [hs];
      _ = 2 * s + 1 := by ring
  use n

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha := Int.even_or_odd a
  obtain hb := Int.even_or_odd b
  obtain hc := Int.even_or_odd c
  obtain ha1 | ha2 := ha
  · obtain hb1 | hb2 := hb
    · left
      obtain ⟨s, hs⟩ := ha1
      obtain ⟨t, ht⟩ := hb1
      use s - t
      calc
        a - b = 2 * s - (2 * t) := by rw [hs, ht]
        _ = 2 * (s - t) := by ring
    · obtain hc1 | hc2 := hc
      · right; left
        obtain ⟨s, hs⟩ := ha1
        obtain ⟨u, hu⟩ := hc1
        use s + u
        calc
          a + c = 2 * s + 2 * u := by rw [hs, hu]
          _ = 2 * (s + u) := by ring
      · right; right
        obtain ⟨t, ht⟩ := hb2
        obtain ⟨u, hu⟩ := hc2
        use t - u
        calc
          b - c = (2 * t + 1) - (2 * u + 1) := by rw [ht, hu]
          _ = 2 * (t - u) := by ring
  · obtain hb1 | hb2 := hb
    · obtain hc1 | hc2 := hc
      · right; right
        obtain ⟨t, ht⟩ := hb1
        obtain ⟨u, hu⟩ := hc1
        use t - u
        calc
          b - c = 2 * t - 2 * u := by rw [ht, hu]
          _ = 2 * (t - u) := by ring
      · right; left
        obtain ⟨s, hs⟩ := ha2
        obtain ⟨u, hu⟩ := hc2
        use s + u + 1
        calc
          a + c = (2 * s + 1) + (2 * u + 1) := by rw [hs, hu]
          _ = 2 * (s + u + 1) := by ring
    · left
      obtain ⟨s, hs⟩ := ha2
      obtain ⟨t, ht⟩ := hb2
      use s - t
      calc
        a - b = (2 * s + 1) - (2 * t + 1) := by rw [hs, ht]
        _ = 2 * (s - t) := by ring
