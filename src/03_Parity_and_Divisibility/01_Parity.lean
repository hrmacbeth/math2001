/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import library.parity
import tactics.addarith
import tactics.inequalities
import tactic.interval_cases

open int


example : odd (7:ℤ) :=
begin
  dsimp [odd],
  use 3,
  norm_num1,
end


example : odd (-3:ℤ) :=
begin
  sorry,
end


example {n : ℤ} (hn : odd n) : odd (3 * n + 2) :=
begin
  dsimp [odd] at *,
  cases hn with k hk,
  use 3 * k + 2,
  calc 3 * n + 2 = 3 * (2 * k + 1) + 2 : by rw [hk]
  ... = 2 * (3 * k + 2) + 1 : by ring
end


example {n : ℤ} (hn : odd n) : odd (7 * n - 4) :=
begin
  sorry,
end



example {x y : ℤ} (hx : odd x) (hy : odd y) : odd (x + y + 1) :=
begin
  cases hx with a ha,
  cases hy with b hb,
  use a + b + 1,
  calc x + y + 1 = (2 * a + 1) + (2 * b + 1) + 1 : by rw [ha, hb]
  ... = 2 * (a + b + 1) + 1 : by ring,
end


example {x y : ℤ} (hx : odd x) (hy : odd y) : odd (x * y + 2 * y) :=
begin
  sorry,
end


example {m : ℤ} (hm : odd m) : even (3 * m - 5) :=
begin
  sorry,
end


example {n : ℤ} (hn : even n) : odd (n ^ 2 + 2 * n - 5) :=
begin
  sorry,
end


example (n : ℤ) : even (n ^ 2 + 3 * n + 4) :=
begin
  cases int.even_or_odd n with hn hn,
  cases hn with x hx,
  use 2 * x ^ 2 + 3 * x + 2,
  calc n ^ 2 + 3 * n + 4 = (2 * x) ^ 2 + 3 * (2 * x) + 4 : by rw hx
  ... = 2 * (2 * x ^ 2 + 3 * x + 2) : by ring,
  cases hn with x hx,
  use 2 * x ^ 2 + 5 * x + 4,
  calc n ^ 2 + 3 * n + 4 = (2 * x + 1) ^ 2 + 3 * (2 * x + 1) + 4 : by rw hx
  ... = 2 * (2 * x ^ 2 + 5 * x + 4) : by ring,
end


example : odd (-9:ℤ) :=
begin
  sorry,
end


example : even (26:ℤ) :=
begin
  sorry,
end


example {m n : ℤ} (hm : odd m) (hn : even n) : odd (n + m) :=
begin
  sorry,
end


example {x : ℤ} (hx : odd x) : odd (x ^ 3) :=
begin
  sorry,
end 


example {x y : ℤ} (hx : odd x) (hy : odd y) : odd (x * y) :=
begin
  sorry,
end


example (n : ℤ) : odd (5 * n ^ 2 + 3 * n + 7) :=
begin
  sorry,
end


example (n : ℤ) : ∃ m ≥ n, odd m :=
begin
  sorry,
end


example (a b c : ℤ) : even (a - b) ∨ even (a + c) ∨ even (b - c) :=
begin
  sorry,
end
