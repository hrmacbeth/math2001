import Mathlib.Data.Real.Basic
import Math2001.Library.Parity
import Math2001.Tactic.Addarith
import Math2001.Tactic.ModCases
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option push_neg.use_distrib true
notation3 "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

namespace Int

/-! # Practice midterm -/

example {a b : ℝ} (h1 : a + b ≤ -2) (h2 : a + 4 * b ≤ 9) : a + 2 * b < 2 :=
  sorry

example : forall_sufficiently_large n : ℤ, n ^ 3 - 11 * n ^ 2 - 5 * n > 0 := by
  dsimp
  sorry

example (n : ℤ) : n ^ 2 - n + 1 ≡ 0 [ZMOD 3] ↔ n ≡ 2 [ZMOD 3] := by
  sorry

example : ∀ x : ℝ, ∃ y : ℝ, x = y + 1 := by
  sorry

example : ¬(∃ x : ℝ, ∀ y : ℝ, x = y + 1) := by
  sorry

example : ¬(∃ N : ℤ, ∀ n ≥ N, Odd n) := by
  sorry
