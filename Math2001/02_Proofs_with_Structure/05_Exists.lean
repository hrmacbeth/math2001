/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' :=
      calc
           x * (-t) = -x * t := by ring
                  _ > 0 := by addarith [hxt]
    cancel x at hxt'
    apply ne_of_lt
    addarith [hxt']

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  · calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by addarith [h]
  · calc
      q = (q + q) / 2 := by ring
      _ > (p + q) / 2 := by addarith [h]


example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use - 0.5
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0, 0
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x/2 + 1
  calc
    (x / 2 + 1) ^ 2 = x ^ 2 / 4 + x + 1 := by ring
                  _  ≥ x + 1 := by extra
                  _  > x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, hxt⟩ := h
  have H := le_or_gt a 1
  have hxt' : (a -1) * (t - 1) < 0 := by
    calc
      (a - 1) * (t - 1) = a * t - a - t + 1 := by ring
                     _ < 0 := by addarith [hxt]
  have hxt'' : -(a - 1) * (t - 1) > 0 := by addarith [hxt']
  have hxt''' : (a - 1) * -(t - 1) > 0 := by
    calc
       (a - 1) * -(t - 1) = -(a - 1) * (t - 1) := by ring
                      _ > 0 := by addarith [hxt'']

  obtain ha1 | ha2 := H
  · apply ne_of_gt
    have ha' : - (a - 1) ≥ 0 := by addarith [ha1]
    cancel -(a- 1) at hxt''
    calc
      t = 1 + (t - 1) := by ring
      _ > 1 := by addarith [hxt'']

  · apply ne_of_lt
    have ha' : (a - 1) > 0 := by addarith [ha2]
    cancel (a- 1) at hxt'''
    have hxt'''' : t - 1 < 0 := by addarith [hxt''']
    calc
      t = 1 + (t - 1) := by ring
      _ < 1 := by addarith [hxt'''']


example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  have h3 := le_or_succ_le a 2
  obtain ha3 | ha4 := h3
  · apply ne_of_lt
    calc
      m = 2 * a := by rw [ha]
      _ ≤ 2 * 2 := by rel [ha3]
      _ = 4 := by ring
      _ < 5 := by numbers
  · apply ne_of_gt
    calc
      m = 2 * a := by rw [ha]
      _ ≥ 2 * 3 := by rel [ha4]
      _ = 6 := by ring
      _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a) / 2, (a + c - b) / 2, (a + b - c) / 2
  constructor
  addarith [ha]
  constructor
  addarith [hb]
  constructor
  addarith [hc]
  constructor
  ring
  constructor
  ring
  ring
