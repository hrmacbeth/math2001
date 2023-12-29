/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import AutograderLib

set_option push_neg.use_distrib true
set_option pp.funBinderTypes true
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
open Function


/-! # Homework 8

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-8
for clearer statements and any special instructions. -/


namespace Nat

@[autograded 5]
theorem problem1 (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  sorry

end Nat


def pascal : ℕ → ℕ → ℕ
  | a, 0 => 1
  | 0, b + 1 => 1
  | a + 1, b + 1 => pascal (a + 1) b + pascal a (b + 1)
termination_by _ a b => a + b

@[autograded 5]
theorem problem2 (m n : ℕ) : pascal m n = pascal n m := by
  match m, n with
  | 0, 0 => rw [pascal]
  | a + 1, 0 => rw [pascal, pascal]
  | 0, b + 1 => rw [pascal, pascal]
  | a + 1, b + 1 =>
    sorry
termination_by _ a b => a + b


@[autograded 4]
theorem problem4a : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry

@[autograded 4]
theorem problem4b : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry


namespace Int

@[autograded 5]
theorem problem5a : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

@[autograded 5]
theorem problem5b : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

end Int


@[autograded 5]
theorem problem6a : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry

@[autograded 5]
theorem problem6b : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry
