/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import library.modular
import library.parity
import tactics.addarith
import tactics.inequalities
import tactics.modular
import tactics.norm_num
import tactic.interval_cases

local attribute [-norm_num] norm_num.eval_nat_int_ext
local attribute [-simp] nat.not_two_dvd_bit1 two_dvd_bit0


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y :=
begin
  have : y ≤ 0 ∨ 0 < y := by apply le_or_lt,
  cases this with H H,
  { have : ¬ (0 < x * y),
    { apply not_lt_of_ge,
      calc 0 = x * 0 : by ring
      ... ≥ x * y : by ineq_tac [H] },
    contradiction },
  exact H,
end


def prime (p : ℕ) : Prop := 2 ≤ p ∧ ∀ (m : ℕ) (hm : m ∣ p), m = 1 ∨ m = p

lemma prime_test {p : ℕ} (hp : 2 ≤ p) (H : ∀ (m : ℕ), 1 < m → m < p → ¬ (m ∣ p)) : prime p :=
begin
  split,
  { apply hp },
  intros m hmp,
  have hp' : 0 < p := by ineq_tac [],
  have h1m : 1 ≤ m := nat.pos_of_dvd_of_pos hmp hp',
  cases eq_or_lt_of_le h1m with hm hm_left,
  { left,
    addarith hm, },
  sorry,
end


example : prime 5 :=
begin
  apply prime_test,
  norm_num,
  intros m hm_left hm_right,
  apply nat.not_dvd_of_exists_lt_and_lt,
  ineq_tac [],
  interval_cases m,
  { use 2,
    split; norm_num1 },
  { use 1,
    split; norm_num1 },
  { use 1,
    split; norm_num1 },
end


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 :=
begin
  have H : (7:ℤ) < 3,
  calc 7 = t : by addarith h
  ... < 3 : h2,
  have : ¬ ((7:ℤ) < 3) := by norm_num1,
  contradiction,
end


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 :=
begin
  have H : (7:ℤ) < 3,
  calc 7 = t : by addarith h
  ... < 3 : h2,
  norm_num1 at H, -- this is a contradiction!
end


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) : n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] :=
begin
  mod_cases n 3,
  { -- case 1: `n ≡ 0 [ZMOD 3]`
    left,
    apply h, }, -- contradiction!
  { -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
    calc (0:ℤ) ≡ 0 + 3 * 1 [ZMOD 3] : by symmetry; apply int.modeq_add_fac'
    ... = 1 ^ 2 + 1 + 1: by norm_num
    ... ≡ n ^ 2 + n + 1 [ZMOD 3] : by mod_rw h
    ... ≡ 1 [ZMOD 3] : hn,
    norm_num1 at H, },
  { -- case 3: `n ≡ 2 [ZMOD 3]`
    right,
    apply h },
end


example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) :
  3 ≤ a :=
begin
  sorry,
end


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
  y ≤ x :=
begin
  sorry,
end


example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] :=
begin
  sorry,
end


example : prime 7 :=
begin
  sorry,
end


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 :=
begin
  have : x = 2 ∨ x + 2 = 0,
  { sorry },
  sorry,
end


open nat

example (p : ℕ) (h : prime p) : p = 2 ∨ odd p :=
begin
  sorry,
end
