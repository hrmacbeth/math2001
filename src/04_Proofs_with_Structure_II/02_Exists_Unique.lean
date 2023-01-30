/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Library.Parity
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel.IneqRel

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  sorry

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 : a = 0
  · calc
      a = (a - -a) / 2 := by ring
      _ = 0 := by addarith [h1]  
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ ∃ q : ℤ, 14 = 5 * q + r := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have : 1 < q
  · apply lt_of_mul_lt_mul_left
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q + r - r := by rw [hr3]
      _ = 5 * q := by ring
    numbers
  have : q < 3
  · apply lt_of_mul_lt_mul_left
    calc
      5 * q = 5 * q + r - r := by ring
      _ = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
    numbers
  interval_cases q
  addarith [hr3]


example (n : ℤ) : Even n ∨ Odd n := by
  sorry

example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  · numbers
  intro y hy
  calc
    y = (4 * y - 3 + 3) / 4 := by ring
    _ = (9 + 3) / 4 := by rw [hy]
    _ = 3 := by numbers


example : ∃! n : ℕ, ∀ a, n ≤ a := by
  sorry

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ ∃ q : ℤ, 11 = 3 * q + r := by
  sorry

def Int.ModEq (n a b : ℤ) : Prop := n ∣ a - b

notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

example {a b : ℤ} (hb : 0 < b) : ∃ z, 0 ≤ z ∧ z < b ∧ a ≡ z [ZMOD b] := by
  sorry
