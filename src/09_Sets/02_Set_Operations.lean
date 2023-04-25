import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Math2001.Library.ParityModular
import Math2001.Tactic.Addarith
import Math2001.Tactic.Define
import Math2001.Tactic.ModCases
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option push_neg.use_distrib true
open Set

attribute [-simp] Set.setOf_eq_eq_singleton



example (t : ℝ) : t ∈ { x : ℝ | -1 < x } ∪ { x : ℝ | x < 1 } := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  dsimp
  intro n
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
    · right
      left
      apply h
    · right
      right
      apply h
  · intro h
    sorry -- can't be bothered typing out the rest



example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  dsimp
  tauto



example : { n : ℕ | 4 ≤ n } ∩ { n : ℕ | n < 7 } = {4, 5, 6} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    interval_cases n <;> tauto
  · intro h
    obtain h4 | h5 | h6 := h
    · constructor <;> addarith [h4]
    · constructor <;> addarith [h5]
    · constructor <;> addarith [h6]


namespace Int
example : { n : ℤ | Even n }ᶜ = { n : ℤ | Odd n} := by
  dsimp
  intro n
  rw [odd_iff_not_even]
end Int

/-! # Exercises -/


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = sorry := by
  dsimp
  tauto


example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = sorry := by
  dsimp
  intro x
  constructor
  · intro h
    obtain ⟨(h1 | h1 | h1 | h1 | h1), (h2 | h2 | h2 | h2 | h2)⟩ := h <;> tauto <;> addarith [h1, h2]
  · intro h
    tauto


example : { n : ℤ | 5 ∣ n } ∩ { n : ℤ | 8 ∣ n } ⊆ { n : ℤ | 40 ∣ n } := by
  sorry

example : { n : ℤ | 3 ∣ n } ∪ { n : ℤ | 2 ∣ n } ⊆ { n : ℤ | n ^ 2 ≡ 1 [ZMOD 6] }ᶜ := by
  sorry
