/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.algebra
import tactics.small_nums

/-! # Lean lab 1

## Summary

We practice tactics for doing high school algebra problems:
* `add_both_sides`
* `mul_both_sides`
* `exact_mod_ring`
* `ring`
* `substitute`
and a couple of more general tactics,
* `have` 
* `calc`
-/


/-! Example 1 -/

example {x : ℤ} (hx : x + 4 = 2) : x = -2 :=
begin
  add_both_sides (-4:ℤ) at hx,
  exact_mod_ring hx,
end

/-! Example 2 -/

example {x : ℝ} (hx : x + 4 = 2) : x = -2 :=
begin
  add_both_sides (-4:ℝ) at hx,
  exact_mod_ring hx,
end

example {x : ℝ} (hx : x + 4 = 2) : x = -2 :=
begin
  calc x = (x + 4) - 4 : by ring
  ... = 2 - 4 : by substitute [hx]
  ... = -2 : by ring
end

/-! Example 3 -/

example {x y : ℚ} (h : x = 2 * y + 1) : 3 * x - 1 = 2 * (3 * y + 1) :=
begin
  calc 3 * x - 1 = 3 * (2 * y + 1) - 1 : by substitute [h]
  ... = 2 * (3 * y + 1) :  by ring
end

/-! Example 4 -/

example {p : ℝ} (hp : 3 * p + 1 = 5 * p - 3) : p = 2 :=
begin
  add_both_sides (-5 * p - 1) at hp,
  mul_both_sides (1/(-2) : ℝ) at hp,
  exact_mod_ring hp,
end

example {p : ℝ} (hp : 3 * p + 1 = 5 * p - 3) : p = 2 :=
begin
  have h : 2 * p = 4,
  { calc 2 * p = (5 * p - 3) - 3 * p + 3 : by ring
    ... = (3 * p + 1) - 3 * p + 3 : by substitute [← hp]
    ... = 4 : by ring },
  mul_both_sides (1/2 : ℝ) at h,
  exact_mod_ring h,
end
