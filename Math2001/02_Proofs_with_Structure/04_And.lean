/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨h1, h2⟩ := hp'
  calc  p ≥ -3 := by addarith [h1]
        _ ≥ -5 := by numbers

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra

  have h3 : b ^ 2 = 0
  · apply le_antisymm
    calc
      b ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra

  constructor
  · cancel 2 at h2
  . cancel 2 at h3

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
            _ ≤ 1 + 3 := by rel [h1, h2]
            _ = 4 := by numbers

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * r = (r + s) + (r - s) := by ring
        _ ≤ 1 + 5 := by rel [h1, h2]
        _ = 6 := by numbers

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc
    m ≤ n - 5 := by addarith [h2]
    _ ≤ 8 - 5 := by addarith [h1]
    _ = 3 := by numbers

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have hp' : p ≥ 7 := by addarith [hp]
  constructor
  · calc
      p ^ 2 ≥ 7 ^ 2 := by rel [hp']
          _ = 49 := by numbers
  · exact hp'


example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h' : a ≥ 6 := by addarith [h]
  constructor
  · exact h'
  · calc
      3 * a ≥ 3 * 6 := by rel [h']
          _ = 18 := by numbers
          _ ≥ 10 := by numbers

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have h3 : y = 2 :=
    calc
      y = (x + 2 * y) - (x + y) := by ring
        _ = 7 - 5 := by rw [h1, h2]
        _ = 2 := by ring


example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by

  have h3 : a * (b - 1) = 0 := by
    calc
      a * (b - 1) = a * b - a := by ring
              _ = 0 := by addarith [h1]

  have h4 := eq_zero_or_eq_zero_of_mul_eq_zero h3
  obtain h5 | h6 := h4
  · left
    constructor
    . apply h5
    · calc
        b = a * b := by rw [h2]
        _ = 0 * b := by rw [h5]
        _ = 0 := by ring
  · right
    constructor
    · have h7 :  b = 1 := by addarith [h6]
      calc
        a = a * 1 := by ring
        _ = a * b := by rw [h7]
        _ = b := by rw [h2]
        _ = 1 := by addarith [h6]
    · addarith [h6]
