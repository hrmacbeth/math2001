/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import tactics.algebra
import tactics.small_nums
import tactics.push_neg
import data.int.parity

/-! # Lean lab 3

## Summary

We practice the tactics of the previous lab for dealing with more complicated logic within proofs:
* `dsimp` (for inspecting definitions)
* `cases` (for breaking up a hypothesis with an `∃` or an `∨`)
* `use` (for proving an existential)

and add a few more:
* `contraposition!` (for contraposition)
* `rw` (for changing a goal or hypothesis to a form known, by an earlier lemma, to be equivalent)
-/


example {n : ℤ} (hn : even (5 * n)) : even n :=
begin
  dsimp [even] at *,
  cases hn with a ha,
  use a - 2 * n,
  calc n = 5 * n - 4 * n : by ring
  ... = 2 * a - 4 * n : by substitute [ha]
  ...= 2 * (a - 2 * n) : by ring,
end

example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n :=
begin
  dsimp [(∣)] at *,
  cases hn with a ha,
  use -3 * a + 2 * n,
  calc n = -3 * (5 * n) + 16 * n : by ring
  ... = -3 * (8 * a) + 16 * n : by substitute [ha]
  ... = 8 * ((-3) * a + 2 * n) : by ring
end

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n :=
begin
  sorry
end

example {n : ℤ} (h2 : 5 ∣ n) (h1 : 8 ∣ n) : 40 ∣ n :=
begin
  dsimp [(∣)] at *,
  cases h1 with a ha,
  cases h2 with b hb,
  use -3 * a + 2 * b,
  calc n = -15 * n + 16 * n : by ring
  ... = -15 * (8 * a) + 16 * n : by substitute [ha]
  ... = -15 * (8 * a) + 16 * (5 * b) : by substitute [hb]
  ... = 40 * (-3 * a + 2 * b) : by ring,
end

-- back to the first example, but now let's use contraposition
example {n : ℤ} (hn : even (5 * n)) : even n :=
begin
  contraposition! hn,
  rw ← int.odd_iff_not_even,
  rw ← int.odd_iff_not_even at hn,
  cases hn with a ha,
  use 5 * a + 2,
  calc 5 * n = 5 * (2 * a + 1) : by substitute [ha]
  ... = 2 * (5 * a + 2) + 1 : by ring,
end

example {x : ℤ} (hx : even (x ^ 2 - 6 * x + 5)) : odd x :=
begin
  contraposition! hx,
  rw ← int.odd_iff_not_even,
  rw ← int.even_iff_not_odd at hx,
  cases hx with a ha,
  use 2 * a ^ 2 - 6 * a + 2,
  calc x ^ 2 - 6 * x + 5 = (2 * a) ^ 2 - 6 * (2 * a) + 5 : by substitute [ha]
  ... = 2 * (2 * a ^ 2 - 6 * a + 2) + 1 : by ring,
end