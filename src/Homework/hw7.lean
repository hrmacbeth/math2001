/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option linter.unusedVariables false
set_option pp.unicode.fun true
set_option push_neg.use_distrib true
open Function


/-! # Homework 7 -/


/- 4 points -/
theorem problem2a : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry

/- 4 points -/
theorem problem2b : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry


/- 5 points -/
theorem problem3a : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

/- 5 points -/
theorem problem3b : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

/- 4 points -/
theorem problem4a : ∀ (f : ℚ → ℚ) (hf : Injective f), Injective (fun x ↦ f x + 1) := by
  sorry

/- 4 points -/
theorem problem4b : ¬ ∀ (f : ℚ → ℚ) (hf : Injective f), Injective (fun x ↦ f x + 1) := by
  sorry


/- 4 points -/
theorem problem5a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry

/- 4 points -/
theorem problem5b : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry


/- 4 points -/
theorem problem6 {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry
