/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Define
import Math2001.Tactic.ExistsDelaborator
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option push_neg.use_distrib true
set_option quotPrecheck false
open Set

attribute [-simp] Set.setOf_eq_eq_singleton


/-! # Homework 9 -/


/- 4 points -/
theorem problem1 : { r : ℤ | r ≡ 7 [ZMOD 10] } 
    ⊆ { s : ℤ | s ≡ 1 [ZMOD 2] } ∩ { t : ℤ | t ≡ 2 [ZMOD 5] } := by
  sorry

local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]  

/- 2 points -/
theorem problem21a : Reflexive (· ∼ ·) := by
  sorry

/- 2 points -/
theorem problem21b : ¬ Reflexive (· ∼ ·) := by
  sorry

/- 2 points -/
theorem problem22a : Symmetric (· ∼ ·) := by
  sorry

/- 2 points -/
theorem problem22b : ¬ Symmetric (· ∼ ·) := by
  sorry

/- 3 points -/
theorem problem23a : AntiSymmetric (· ∼ ·) := by
  sorry

/- 3 points -/
theorem problem23b : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

/- 3 points -/
theorem problem24a : Transitive (· ∼ ·) := by
  sorry

/- 3 points -/
theorem problem24b : ¬ Transitive (· ∼ ·) := by
  sorry

