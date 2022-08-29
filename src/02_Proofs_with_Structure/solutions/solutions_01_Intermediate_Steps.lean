/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.inequalities

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
begin
  have h3 : 0 ≤ b + a,
  addarith [h1],
  have h4 : 0 ≤ b - a,
  addarith [h2],
  calc a ^ 2 = a ^ 2 + 0 : by ring
  ... ≤ a ^ 2 + (b + a) * (b - a) : by ineq_tac []
  ... = b ^ 2 : by ring
end
