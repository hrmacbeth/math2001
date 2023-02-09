/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Math2001.Library.ParityModular
import Math2001.Library.Prime
import Math2001.Tactic.Addarith
import Math2001.Tactic.ModCases
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h | h : k ≤ 4 ∨ 5 ≤ k := le_or_lt k 4
  · have :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h]
    numbers at this
  · sorry

example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at this


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  sorry

theorem Int.even_iff_not_odd (n : ℤ) : Even n ↔ ¬ Odd n := by
  constructor
  · intro h1 h2
    have : Even n ∧ Odd n := ⟨h1, h2⟩
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1.symm]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at this
    done
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction   


theorem Int.odd_iff_not_even (n : ℤ) : Odd n ↔ ¬ Even n := by
  sorry

example (n : ℕ) : ¬((n:ℤ) ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : (n:ℤ) % 3
  · have :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ (n:ℤ) ^ 2 [ZMOD 3] := by rel [hn.symm]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at this
    done
  · sorry
  · sorry

example (a : ℤ) {b : ℤ} (hb : 0 < b)
    (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have h₂ : k < q + 1
  · apply lt_of_mul_lt_mul_left (a := b)
    calc b * k = a := by rw [hk]
      _ < b * (q + 1) := hq₂
    extra
  have h₁ : ¬ (k < q + 1)
  · sorry
  sorry

lemma better_prime_test {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2) 
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intros m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · sorry
  have hl1 : 1 < l
  · apply lt_of_mul_lt_mul_left (a := m)
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
    extra
  have hl2 : l < T
  · sorry
  have : ¬ l ∣ p := by apply H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intros m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  · extra
  interval_cases m
  · take 39
    constructor <;> numbers
  · take 26
    constructor <;> numbers
  · take 19
    constructor <;> numbers
  · sorry
  · sorry
  · sorry
  · sorry

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3  ≥ 30) := by
  sorry

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  sorry

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  sorry

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  sorry

example (n : ℕ) : ¬((n:ℤ) ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry
example : Prime 97 := by
  sorry
