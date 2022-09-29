import tactic.norm_num
import tactic.ring
import tactic.ring_exp
import algebra.divisibility
import data.nat.parity

local attribute [-norm_num] norm_num.eval_nat_int_ext


example : (11:ℕ) ∣ 88 :=
begin
  dsimp [(∣)],
  use 8,
  norm_num1,
end


example : (-2:ℤ) ∣ 6 :=
begin
  sorry,
end


example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b :=
begin
  cases hab with k hk,
  use k * (a * k + 2),
  calc b ^ 2 + 2 * b = (a * k) ^ 2 + 2 * (a * k) : by rw [hk]
  ... = a * (k * (a * k + 2)) : by ring 
end


example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c :=
begin
  sorry,
end 



example {x y z : ℕ} (h : (x * y) ∣ z) : x ∣ z :=
begin
  sorry,
end


example (t : ℤ) : t ∣ 0 :=
begin
  sorry,
end


example {a b : ℤ} (hab : a ∣ b) : a ∣ (3 * b ^ 3 - b ^ 2 + 5 * b) :=
begin
  sorry,
end


example {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c :=
begin
  sorry,
end


example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 :=
begin
  sorry,
end



example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b :=
begin
  sorry,
end
