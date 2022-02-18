import tactics.algebra
import tactics.small_nums
import tactics.push_neg
import data.int.parity
import data.real.sqrt


/- problem 1 -/
example (a : ℤ) : odd (a ^ 2 + 4 * a + 5) ↔ even a :=
begin
  split,
  { sorry, },
  { sorry, },
end

/- problem 2 -/
example (n : ℤ) : 7 ∣ 10 * n ↔ 7 ∣ n :=
begin
  split,
  { sorry, },
  { sorry },
end

/- problem 3; the lemma `mul_eq_zero` may be useful -/
example (x y : ℝ) : x ^ 3 + x ^ 2 * y = y ^ 2 + x * y ↔ y = x ^ 2 ∨ y = - x :=
begin
  split,
  { sorry, },
  { sorry, }
end

/- problem 7; the lemma `real.lt_sqrt` may be useful -/
example : ∃ x > 0, x ^ 2 < real.sqrt x :=
begin
  sorry
end

/- problem 8 -/
example : ∃ n : ℕ, 11 ∣ 2 ^ n - 1 :=
begin
  sorry
end

