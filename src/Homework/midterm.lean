import Mathlib.Data.Real.Basic
import Math2001.Library.Parity
import Math2001.Library.Prime
import Math2001.Tactic.Addarith
import Math2001.Tactic.ModCases
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option linter.unusedVariables false
set_option push_neg.use_distrib true
notation3 "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

namespace Int

/-! # Midterm -/

example {x y : ℚ} (h1 : x - 2 * y ≤ 2) (h2 : x + y ≤ 4) : x < 4 :=
  sorry

example {n : ℤ} (h : n ^ 2 + 3 * n - 2 ≡ 0 [ZMOD 4]) : n ≡ 2 [ZMOD 4] ∨ n ≡ 3 [ZMOD 4] := by
  sorry

example : forall_sufficiently_large t : ℝ, t ^ 3 ≥ 8 * t ^ 2 - 4 * t + 1 := by
  dsimp
  sorry

example {x y z : ℤ} (h1 : Even (x + y)) : Even (x + z) ↔ Even (y + z) := by
  sorry

example : ¬ ∀ a b : ℕ, Prime (a * b + 1) := by
  sorry

example : ¬ ∃ a : ℕ, ∀ b : ℕ, Prime (a * b + 1) := by
  sorry
