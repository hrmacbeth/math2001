/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import AutograderLib

set_option push_neg.use_distrib true
set_option pp.funBinderTypes true
attribute [-simp] ne_eq
attribute [-ext] Prod.ext
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
open Function


/-! # Homework 9

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-9
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry

@[autograded 4]
theorem problem2a : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry

@[autograded 4]
theorem problem2b : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry


@[autograded 4]
theorem problem3 : Surjective (fun ((a, b) : ℚ × ℕ) ↦ a ^ b) := by
  sorry

@[autograded 4]
theorem problem4 :
    ¬Injective (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  sorry

@[autograded 4]
theorem problem5 : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  sorry

@[autograded 4]
theorem problem6 : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a, b) ↦ (sorry, sorry)
  sorry
