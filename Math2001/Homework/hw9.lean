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

@[autograded 3]
theorem problem1 {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  sorry

@[autograded 4]
theorem problem2a : Bijective (fun (x : ℝ) ↦ 5 + 3 * x) := by
  sorry

@[autograded 4]
theorem problem2b : ¬ Bijective (fun (x : ℝ) ↦ 5 + 3 * x) := by
  sorry

@[autograded 5]
theorem problem3 :
    ¬Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x - 2 * y + z)) := by
  sorry

@[autograded 4]
theorem problem4 : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r + 2 * s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a, b) ↦ (sorry, sorry)
  sorry

@[autograded 4]
theorem problem5 : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  sorry

@[autograded 5]
theorem problem6 : Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 - y ^ 2) := by
  sorry
