/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.int.parity
import tactics.algebra
import tactics.small_nums

/-! # Lean lab 2

## Summary

We learn tactics for dealing with more complicated logic within proofs:
* `dsimp` (for inspecting definitions)
* `cases` (for breaking up a hypothesis with an `∃` or an `∨`)
* `use` (for proving an existential)
-/


example {n : ℤ} (hn : odd n) : odd (3 * n + 2) :=
begin
  dsimp [odd] at *,
  cases hn with k hk,
  use 3 * k + 2,
  calc 3 * n + 2 = 3 * (2 * k + 1) + 2 : by substitute [hk]
  ... = 2 * (3 * k + 2) + 1 : by ring
end

example {n : ℤ} (hn : odd n) : odd (7 * n - 4) :=
begin
  dsimp [odd] at *,
  cases hn with k hk,
  use 7 * k + 1,
  calc 7 * n - 4 = 7 * (2 * k + 1) - 4 : by substitute [hk]
  ... = 2 * (7 * k + 1) + 1 : by ring
end

example {n : ℤ} (hn : odd n) : even (3 * n - 5) :=
begin
  sorry
end

example {m n : ℤ} (hm : odd m) (hn : even n) : odd (n + m) :=
begin
  sorry
end

example {a b : ℕ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b :=
begin
  dsimp [(∣)] at *,
  cases hab with k hk,
  use k * (a * k + 2),
  calc b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) : by substitute [hk]
  ... = a * (k * (a * k + 2)) : by ring 
end

example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c :=
begin
  sorry
end 

example {a b c : ℕ} (habc : (a * b) ∣ c) : a ∣ c :=
begin
  sorry
end

-- parity cases
example {m n : ℤ} (hmn : odd m ↔ even n) : even (m * n) :=
begin
  cases int.even_or_odd m with hm hm,
  { rw [even] at *,
    cases hm with k hk,
    use k * n,
    calc m * n = (2 * k) * n : by substitute [hk]
    ... =  2 * (k * n) : by ring },
  { rw hmn at hm,
    rw [even] at *,
    cases hm with k hk,
    use k * m,
    calc m * n = m * (2 * k) : by substitute [hk]
    ... =  2 * (k * m) : by ring },
end

example (n : ℤ) : even (n ^ 2 + 3 * n + 4) :=
begin
  sorry
end