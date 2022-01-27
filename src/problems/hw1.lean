/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.algebra
import tactics.small_nums

/-! # Lean hw 1

This homework will be graded for effort only, on a yes/no basis.  You must upload a file to
Gradescope, but it is fine if you can't solve all the problems.
-/

lemma problem1 {a b : ℤ} (h : a - b = 0) : a = b :=
begin
  sorry
end

lemma problem2 {a : ℚ} (ha : 3 * a + 1 = 4) : a = 1 :=
begin
  sorry
end

lemma problem3 {a b c d e f : ℤ} (h₁ : a * d = b * c) (h₂ : c * f = d * e) :
  d * (a * f - b * e) = 0 :=
begin
  sorry
end

lemma problem4 (l m n : ℤ) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 :=
begin
  sorry
end

lemma problem5 {x y : ℝ} (h₁ : x - y = 4) (h₂ : x * y = 1) : (x + y) ^ 2 = 20 :=
begin
  sorry
end

lemma problem6 {a b : ℝ} (h₁ : a + 2 * b = 4) (h₂ : a - b = 1) : a = 2 :=
begin
  sorry
end

lemma problem7 {x y : ℝ} (hx : x + 3 = 5) (hxy : 2 * x - y * x = 0) : y = 2 :=
begin
  sorry
end
