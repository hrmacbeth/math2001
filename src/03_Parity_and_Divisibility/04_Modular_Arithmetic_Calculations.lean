/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.int.parity
import library.modular
import tactics.modular
import tactics.norm_num'

attribute [irreducible] int.mod


example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
  a * b + b ^ 3 + 3 ≡ 2 [ZMOD 5] :=
calc a * b + b ^ 3 + 3 ≡ 4 * b + b ^ 3 + 3 [ZMOD 5] : by mod_rw [ha]
... ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] : by mod_rw [hb]
... = 2 + 5 * 8 : by norm_num'
... ≡ 2 [ZMOD 5] : by apply int.modeq_add_fac'


example : ∃ a : ℤ, 6 * a ≡ 4 [ZMOD 11] :=
begin
  use 8,
  calc 6 * 8 = 4 + 11 * 4 : by norm_num'
  ... ≡ 4 [ZMOD 11] : by apply int.modeq_add_fac',
end


example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] :=
begin
  mod_cases x 3 with hx,
  calc x ^ 3 ≡ 0 ^ 3 [ZMOD 3] : by mod_rw hx
  ... = 0 : by norm_num'
  ... ≡ x [ZMOD 3] : by mod_rw hx,
  calc x ^ 3 ≡ 1 ^ 3 [ZMOD 3] : by mod_rw hx
  ... = 1 : by norm_num'
  ... ≡ x [ZMOD 3] : by mod_rw hx,
  calc x ^ 3 ≡ 2 ^ 3 [ZMOD 3] : by mod_rw hx
  ... = 2 + 3 * 2 : by norm_num'
  ... ≡ 2 [ZMOD 3] : by apply int.modeq_add_fac'
  ... ≡ x [ZMOD 3] : by mod_rw hx,
end


example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] :=
sorry


example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] :=
sorry

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] :=
begin
  sorry
end


example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] :=
begin
  sorry
end


example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] :=
begin
  sorry
end
