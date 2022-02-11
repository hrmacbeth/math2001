/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import tactics.algebra
import tactics.small_nums
import tactics.push_neg
import data.int.parity

/-! # Lean hw 3 -/

lemma problem5_1 {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n :=
begin
  sorry
end

lemma problem5_2 {n : ℤ} (hn : 7 ∣ 5 * n) : 7 ∣ n :=
begin
  sorry
end

lemma problem6_1 {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n :=
begin
  sorry
end

lemma problem6_2 {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n :=
begin
  sorry
end

lemma problem7 {a b : ℤ} (h : odd (a ^ 2 * (b ^ 2 - 2 * b))) : odd a ∧ odd b :=
begin
  sorry
end

lemma problem9 {a : ℤ} (ha : ¬ (4 ∣ a ^ 2)) : odd a :=
begin
  sorry
end

