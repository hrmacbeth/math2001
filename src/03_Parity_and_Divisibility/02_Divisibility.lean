/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Math2001.Library.Division
import Math2001.Tactic.Rel
import Math2001.Tactic.Numbers
import Math2001.Tactic.Take


example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  take 8
  numbers


example : (-2 : ℤ) ∣ 6 := by
  sorry

example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  take k * (a * k + 2)
  calc
    b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  sorry

example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  sorry

example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  · numbers
  take 2
  constructor
  · numbers
  · numbers


example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H : 1 ≤ k
  · apply pos_of_mul_pos_right (a := a)
    · calc
        0 < b := hb
        _ = a * k := hk
    · extra
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]


example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  sorry

example (t : ℤ) : t ∣ 0 := by
  sorry

example : ¬(3 : ℤ) ∣ -10 := by
  sorry

example {a b : ℤ} (hab : a ∣ b) : a ∣ 3 * b ^ 3 - b ^ 2 + 5 * b := by
  sorry

example {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
  sorry

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  sorry

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  sorry

example (a : ℕ) (h : a ^ 2 ∣ a) : a = 0 ∨ a = 1 := by
  have ha : 0 ≤ a := by extra
  obtain ha | ha := eq_or_lt_of_le ha
  · sorry
  have H1 : a ^ 2 = a
  · sorry
  have H2 : a = 1 ∨ a = 0
  · sorry
  sorry
