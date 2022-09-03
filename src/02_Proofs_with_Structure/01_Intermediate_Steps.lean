/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.inequalities


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) :
  a = 9 :=
begin
  have hb : b = 1,
  addarith h2,
  calc a = (a - 5 * b) + 5 * b : by ring
  ... = 4 + 5 * 1 : by rw [h1, hb]
  ... = 9 : by ring,
end


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) :
  m ≤ 6 :=
begin
  have h3 : m + 3 ≤ 9,
  calc m + 3 ≤ 2 * n - 1 : by sorry
  ... ≤ 2 * 5 - 1 : by sorry
  ... = 9 : by sorry,
  sorry,
end


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : 
  r ≤ 3 :=
begin
  have h3 : r ≤ 3 + s,
  sorry,
  have h4 : r ≤ 3 - s,
  sorry,
  calc r = (r + r) / 2 : by sorry
  ... ≤ ((3 - s) + (3 + s)) / 2 : by sorry
  ... = 3 : by sorry
end


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : 
  y > 3 :=
begin
  sorry
end


example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
begin
  sorry
end

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 :=
begin
  sorry
end
