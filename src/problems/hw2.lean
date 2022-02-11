/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.int.parity
import data.real.basic
import tactics.algebra
import tactics.small_nums

/-! # Lean hw 2 -/

lemma problem1 {x y : ℝ} (h₁ : x - y = 4) (h₂ : x * y = 1) : (x + y) ^ 2 = 20 :=
begin
  sorry
end

lemma problem2 {a b : ℝ} (h₁ : a + 2 * b = 4) (h₂ : a - b = 1) : a = 2 :=
begin
  sorry
end


lemma problem4 {x : ℤ} (hx : odd x) : odd (x ^ 3) :=
begin
  sorry
end 

lemma problem5 {x y : ℤ} (hx : odd x) (hy : odd y) : odd (x * y + 2 * y) :=
begin
  sorry
end

lemma problem6 {a b : ℤ} (hab : a ∣ b) : a ∣ (3 * b ^ 3 - b ^ 2 + 5 * b) :=
begin
  sorry
end

lemma problem7 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c :=
begin
  sorry
end

/- For the next problem, notice the lemma `mul_eq_zero` stating that if the product of two numbers
is zero then one of them must be zero, or alternatively the lemma `mul_eq_mul_left_iff` stating
that if `a * x = a * y` then either `a = 0` or `x = y`. -/

lemma problem8 {x y : ℝ} (hxy : x ^ 2 + 5 * y = y ^ 2 + 5 * x) : x = y ∨ x + y = 5 :=
begin
  sorry
end

/- For the next problem, notice the lemma `int.even_or_odd` stating that an integer is either even
or odd: -/

lemma problem9 (n : ℤ) : odd (5 * n ^ 2 + 3 * n + 7) :=
begin
  sorry
end

/- For the next problem, `int.even_or_odd` may be useful again, or you might use one of the lemmas
`int.odd_iff_not_even`, `int.even_iff_not_odd`saying that even implies not odd, and vice versa. -/

lemma problem10 {a b : ℤ} (h : even a ↔ even b) : even (a + b) :=
begin
  sorry
end
