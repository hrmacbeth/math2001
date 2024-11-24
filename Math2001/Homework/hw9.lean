/- Copyright (c) Heather Macbeth, 2023-4.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

open Function


/-! # Homework 9

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-9,
for clearer statements and any special instructions. -/


/- Problem 1: prove one of these, delete the other -/

@[autograded 4]
theorem problem1a : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry

@[autograded 4]
theorem problem1b : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry


/- Problem 2: prove one of these, delete the other -/

@[autograded 4]
theorem problem2a : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

@[autograded 4]
theorem problem2b : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry


/- Problem 3: prove one of these, delete the other -/

@[autograded 4]
theorem problem3a : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry

@[autograded 4]
theorem problem3b : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry


/- Problem 4: prove one of these, delete the other -/

@[autograded 4]
theorem problem4a : Bijective (fun (x : ℝ) ↦ 3 - 2 * x) := by
  sorry

@[autograded 4]
theorem problem4b : ¬ Bijective (fun (x : ℝ) ↦ 3 - 2 * x) := by
  sorry


/- Problem 5: prove one of these, delete the other -/

@[autograded 5]
theorem problem5a :
    Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  sorry

@[autograded 5]
theorem problem5b :
    ¬Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  sorry


/- Problem 6: prove one of these, delete the other -/

@[autograded 4]
theorem problem6a : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r + 2 * s)) := by
  sorry

@[autograded 4]
theorem problem6b : ¬ Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r + 2 * s)) := by
  sorry
