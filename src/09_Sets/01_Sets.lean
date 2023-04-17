import Mathlib.Data.Real.Basic
import Math2001.Library.Parity
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option push_neg.use_distrib true

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
