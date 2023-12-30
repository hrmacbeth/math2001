/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.2: Proving equalities in Lean

This file should be worked through in parallel with the corresponding section of the book:
https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#proving-equalities-in-lean

I recommend splitting your screen to display the code and the book side by side! -/


-- Example 1.2.1
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring

-- Example 1.2.2.
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by sorry
    _ = -1 - 2 * s := by sorry
    _ = -1 - 2 * 3 := by sorry
    _ = -7 := by sorry

-- Example 1.2.3
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
    (2 * a * n + b * m) ^ 2
      = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by sorry
    _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by sorry
    _ = 2 := by sorry

-- Example 1.2.4.
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  sorry
