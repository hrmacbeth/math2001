import tactics.algebra
import tactics.small_nums
import tactics.push_neg
import data.int.parity
import data.real.sqrt

lemma problem1 (a : ℤ) : odd (a ^ 2 + 4 * a + 5) ↔ even a :=
begin
  split,
  { sorry, },
  { sorry, },
end

lemma problem2 (n : ℤ) : 7 ∣ 10 * n ↔ 7 ∣ n :=
begin
  split,
  { sorry, },
  { sorry },
end

/- the lemma `mul_eq_zero` may be useful -/
lemma problem3 (x y : ℝ) : x ^ 3 + x ^ 2 * y = y ^ 2 + x * y ↔ y = x ^ 2 ∨ y = - x :=
begin
  split,
  { sorry, },
  { sorry, }
end

/- the lemma `real.lt_sqrt` may be useful -/
lemma problem7 : ∃ x > 0, x ^ 2 < real.sqrt x :=
begin
  sorry
end

lemma problem8 : ∃ n : ℕ, 11 ∣ 2 ^ n - 1 :=
begin
  sorry
end
