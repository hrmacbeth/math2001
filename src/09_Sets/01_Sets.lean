import Mathlib.Data.Real.Basic
import Math2001.Library.Parity
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option push_neg.use_distrib true
open Set

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
  dsimp [subset_def]
  intro a ha
  obtain ⟨k, hk⟩ := ha
  take 2 * k
  calc a = 4 * k := hk
    _ = 2 * (2 * k) := by ring


example : ¬ { x : ℝ | 0 ≤ x ^ 2 } ⊆ { t : ℝ | 0 ≤ t } := by
  dsimp [subset_def]
  push_neg
  take -3
  constructor
  · numbers
  · numbers  

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

example : ¬ { a : ℕ | 20 ∣ a } ⊆ { x : ℕ | 5 ∣ x } := by
  sorry


example : { a : ℕ | 5 ∣ a } ⊆ { x : ℕ | 20 ∣ x } := by
  sorry

example : ¬ { a : ℕ | 5 ∣ a } ⊆ { x : ℕ | 20 ∣ x } := by
  sorry

example : { r : ℤ | 3 ∣ r } ⊆ { s : ℤ | 0 ≤ s } := by
  sorry

example : ¬ { r : ℤ | 3 ∣ r } ⊆ { s : ℤ | 0 ≤ s } := by
  sorry

example : { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry

example : ¬ { m : ℤ | m ≥ 10 } ⊆ { n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n } := by
  sorry
