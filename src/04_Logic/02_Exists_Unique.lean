/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import library.arithmetic
import library.parity
import tactics.addarith
import tactics.inequalities
import tactics.positivity
import tactic.interval_cases

open int


example : ∃! a : ℝ, 3 * a + 1 = 7 :=
begin
  use 2,
  split,
  { norm_num1, },
  intros y hy,
  calc y = ((3 * y + 1) - 1) / 3 : by ring
  ... = (7 - 1) / 3 : by rw hy
  ... = 2 : by norm_num1,
end


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 :=
begin
  sorry,
end


example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 :=
begin
  cases hx with a ha, dsimp at ha,
  cases ha with ha1 ha2,
  have h1 : - a = a,
  { apply ha2,
    calc (-a) ^ 2 = a ^ 2 : by ring
    ... = x : ha1 },
  have h2 : a = 0,
  calc a = (a - (-a)) / 2 : by ring
  ... = 0 : by addarith h1,
  calc x = a ^ 2 : by rw ha1
  ... = 0 ^ 2 : by rw h2
  ... = 0 : by ring,
end


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ ∃ q : ℤ, 14 = 5 * q + r :=
begin
  use 4, dsimp,
  split,
  { split,
    norm_num1,
    split,
    norm_num1,
    use 2,
    norm_num1 },
  intros r hr,
  cases hr with hr1 hr2,
  cases hr2 with hr2 hr3,
  cases hr3 with q hr3,
  have : 1 < q,
  { apply lt_of_mul_lt_mul_left,
    calc 5 * 1 < 14 - r : by addarith hr2
    ... = (5 * q + r) - r : by rw hr3
    ... = 5 * q : by ring,
    norm_num1 },
  have : q < 3,
  { apply lt_of_mul_lt_mul_left,
    calc 5 * q = (5 * q + r) - r : by ring
    ... = 14 - r : by rw hr3
    ... < 5 * 3 : by addarith hr1,
    norm_num1 },
  interval_cases q,
  addarith hr3,
end


example (n : ℤ) : even n ∨ odd n :=
begin
  sorry,
end


example : ∃! x : ℚ, 4 * x - 3 = 9 :=
begin
  use 3,
  split,
  { norm_num1, },
  intros y hy,
  calc y = ((4 * y - 3) + 3) / 4 : by ring
  ... = (9 + 3) / 4 : by rw hy
  ... = 3 : by norm_num1,
end


example : ∃! n : ℕ, ∀ a, n ≤ a :=
begin
  sorry,
end


example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ ∃ q : ℤ, 11 = 3 * q + r :=
begin
  sorry,
end


def int.modeq (n a b : ℤ) := n ∣ (a - b)

notation a ` ≡ `:50 b ` [ZMOD `:50 n `]`:0 := int.modeq n a b

example {a b : ℤ} (hb : 0 < b) : ∃ z, 0 ≤ z ∧ z < b ∧ a ≡ z [ZMOD b] :=
begin
  sorry,
end
