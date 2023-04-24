import Mathlib.Data.Real.Basic
import Math2001.Library.Parity
import Math2001.Tactic.Define.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take
import Mathlib.Tactic.LibrarySearch

set_option push_neg.use_distrib true
open Set

notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)


namespace Nat

#check { n : ℤ | n ≤ 3 }


example : 1 ∈ { n : ℤ | n ≤ 3 } := by
  dsimp
  numbers


example : 10 ∉ { n : ℕ | Odd n } := by
  dsimp
  rw [← even_iff_not_odd]
  take 5
  numbers


example : { a : ℕ | 4 ∣ a } ⊆ { b : ℕ | 2 ∣ b } := by
  dsimp
  intro a ha
  obtain ⟨k, hk⟩ := ha
  take 2 * k
  calc a = 4 * k := hk
    _ = 2 * (2 * k) := by ring


example : { x : ℝ | 0 ≤ x ^ 2 } ⊈ { t : ℝ | 0 ≤ t } := by
  dsimp
  push_neg
  take -3
  constructor
  · numbers
  · numbers  


example : { x : ℤ | Int.Odd x } = { a : ℤ | ∃ k, a = 2 * k - 1 } := by
  dsimp
  intro x
  constructor
  · intro h
    obtain ⟨l, hl⟩ := h
    take l + 1
    calc x = 2 * l + 1 := by rw [hl]
      _ = 2 * (l + 1) - 1 := by ring
  · intro h
    obtain ⟨k, hk⟩ := h
    take k - 1
    calc x = 2 * k - 1 := by rw [hk]
      _ = 2 * (k - 1) + 1 := by ring


example : { a : ℕ | 4 ∣ a } ≠ { b : ℕ | 2 ∣ b } := by
  dsimp
  push_neg
  take 6
  right
  constructor
  · apply not_dvd_of_exists_lt_and_lt
    · numbers
    take 1
    constructor <;> numbers
  · take 3
    numbers


example : { n : ℤ | 3 ∣ n } = { n : ℤ | 3 ∣ 5 * n } := by
  dsimp
  intro x
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    take 5 * k
    calc 5 * x = 5 * (3 * k) := by rw [hk]
      _ = 3 * (5 * k) := by ring
  · intro h
    obtain ⟨k, hk⟩ := h
    take 2 * k - 3 * x
    calc
      x = 2 * (5 * x) - 3 * 3 * x := by ring
      _ = 2 * (3 * k) - 3 * 3 * x := by rw [hk] 
      _ = 3 * (2 * k - 3 * x) := by ring


example : { x : ℝ | x ^ 2 - x - 2 = 0 } = {-1, 2} := by
  dsimp
  intro x
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
        _ = 0 := by rw [h]
    rw [_root_.mul_eq_zero] at hx   
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc x ^ 2 - x - 2 = (-1) ^ 2 - (-1) - 2 := by rw [h]
        _ = 0 := by numbers
    · calc x ^ 2 - x - 2 = 2 ^ 2 - 2 - 2 := by rw [h]
        _ = 0 := by numbers


example : {1, 3, 6} ⊆ { t : ℚ | t < 10 } := by
  dsimp
  intro t ht
  obtain h1 | h3 | h6 := ht
  · addarith [h1]
  · addarith [h3]
  · addarith [h6]

/-! # Exercises -/


example : 4 ∈ { a : ℚ | a < 3 } := by
  sorry

example : 4 ∉ { a : ℚ | a < 3 } := by
  sorry

example : 6 ∈ { n : ℕ | n ∣ 42 } := by
  sorry

example : 6 ∉ { n : ℕ | n ∣ 42 } := by
  sorry


example : 8 ∈ { k : ℤ | 5 ∣ k } := by
  sorry  

example : 8 ∉ { k : ℤ | 5 ∣ k } := by
  sorry

example : 11 ∈ { n : ℕ | Odd n } := by
  sorry

example : 11 ∉ { n : ℕ | Odd n } := by
  sorry


example : -3 ∈ { x : ℝ | ∀ y : ℝ, x ≤ y ^ 2 } := by
  sorry

example : -3 ∉ { x : ℝ | ∀ y : ℝ, x ≤ y ^ 2 } := by
  sorry


example : { a : ℕ | 20 ∣ a } ⊆ { x : ℕ | 5 ∣ x } := by
  sorry

example : { a : ℕ | 20 ∣ a } ⊈ { x : ℕ | 5 ∣ x } := by
  sorry


example : { a : ℕ | 5 ∣ a } ⊆ { x : ℕ | 20 ∣ x } := by
  sorry

example : { a : ℕ | 5 ∣ a } ⊈ { x : ℕ | 20 ∣ x } := by
  sorry

example : { r : ℤ | 3 ∣ r } ⊆ { s : ℤ | 0 ≤ s } := by
  sorry

example : { r : ℤ | 3 ∣ r } ⊈ { s : ℤ | 0 ≤ s } := by
  sorry

example : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry

example : { m : ℤ | m ≥ 10 } ⊈ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry


example : { x : ℝ | x ^ 2 + 3 * x + 2 = 0 } = {-1, -2} := by
  sorry
