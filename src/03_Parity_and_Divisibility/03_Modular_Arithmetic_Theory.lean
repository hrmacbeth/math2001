/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import library.division
import tactic.interval_cases


def int.modeq (n a b : ℤ) := n ∣ (a - b)

notation a ` ≡ `:50 b ` [ZMOD `:50 n `]`:0 := int.modeq n a b


example : 11 ≡ 3 [ZMOD 4] :=
begin
  use 2,
  norm_num,
end


example : -5 ≡ 1 [ZMOD 3] :=
begin
  sorry
end

variables {m n a b c d : ℤ}


lemma int.modeq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
  a + c ≡ b + d [ZMOD n] :=
begin
  dsimp [int.modeq] at *,
  cases h1 with x hx,
  cases h2 with y hy,
  use x + y,
  calc a + c - (b + d) = (a - b) + (c - d) : by ring
  ... = n * x + n * y : by rw [hx, hy]
  ... = n * (x + y) : by ring,
end


lemma int.modeq.sub (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
  a - c ≡ b - d [ZMOD n] :=
begin
  sorry
end


lemma int.modeq.neg (h1 : a ≡ b [ZMOD n]) :
  - a ≡ - b [ZMOD n] :=
begin
  sorry
end


lemma int.modeq.mul (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
  a * c ≡ b * d [ZMOD n] :=
begin
  cases h1 with x hx,
  cases h2 with y hy,
  use x * c + b * y,
  calc a * c - b * d = (a - b) * c + b * (c - d) : by ring
  ... = (n * x) * c + b * (n * y) : by rw [hx, hy]
  ... = n * (x * c + b * y) : by ring,
end


example : ∃ a b c d, a ≡ b [ZMOD 4] ∧ c ≡ d [ZMOD 4] ∧ ¬ a / c ≡ b / d [ZMOD 4] :=
begin
  use [10, 18, 2, 6],
  split,
  use -2,
  norm_num,
  split,
  use -1,
  norm_num,
  apply int.not_dvd_of_exists_lt_and_lt,
  norm_num,
  use 0,
  split,
  norm_num,
  norm_num,
end


lemma int.modeq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] :=
begin
  cases h with x hx,
  use x * (a + b),
  calc a ^ 2 - b ^ 2 = (a - b) * (a + b) : by ring
  ... = (n * x) * (a + b) : by rw hx
  ... = n * (x * (a + b)) : by ring,
end


lemma int.modeq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] :=
begin
  sorry
end


lemma int.modeq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] :=
sorry -- we'll prove this later in the course


lemma int.modeq.refl (a : ℤ) : a ≡ a [ZMOD n] :=
begin
  use 0,
  ring,
end


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
  a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] :=
begin
  cases ha with x hx,
  use x * (b ^ 2 + a * b + 2 * b + 3),
  calc (a * b ^ 2 + a ^ 2 * b + 3 * a) - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2)
      = (a - 2) * (b ^ 2 + a * b + 2 * b + 3) : by ring
  ... = 4 * x * (b ^ 2 + a * b + 2 * b + 3) : by rw hx
  ... = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) : by ring,
end


example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
  a * b ^ 2 + a ^ 2 * b + 3 ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 [ZMOD 4] :=
begin
  apply int.modeq.add,
  apply int.modeq.add,
  apply int.modeq.mul,
  apply ha,
  apply int.modeq.refl,
  apply int.modeq.mul,
  apply int.modeq.pow,
  apply ha,
  apply int.modeq.refl,
  apply int.modeq.refl,
end



example : 34 ≡ 104 [ZMOD 5] :=
begin
  sorry
end


lemma int.modeq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] :=
begin
  sorry
end


lemma int.modeq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
  a ≡ c [ZMOD n] :=
begin
  sorry
end


lemma int.modeq_add_fac' : a + n * c ≡ a [ZMOD n] :=
begin
  sorry
end


example : ∃ a b c d, a ≡ b [ZMOD 4] ∧ c ≡ d [ZMOD 4] ∧ ¬ a / c ≡ b / d [ZMOD 4] :=
begin
  sorry,
end


example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
  4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] :=
begin
  sorry
end
