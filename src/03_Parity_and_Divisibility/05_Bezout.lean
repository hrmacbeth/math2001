import tactic.ring

local attribute [-norm_num] norm_num.eval_nat_int_ext


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n :=
begin
  cases hn with a ha,
  use -3 * a + 2 * n,
  calc n = -3 * (5 * n) + 16 * n : by ring
  ... = -3 * (8 * a) + 16 * n : by rw [ha]
  ... = 8 * (-3 * a + 2 * n) : by ring
end


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n :=
begin
  sorry,
end


example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n :=
begin
  sorry,
end


example {m : ℤ} (h2 : 5 ∣ m) (h1 : 8 ∣ m) : 40 ∣ m :=
begin
  cases h1 with a ha,
  cases h2 with b hb,
  use -3 * a + 2 * b,
  calc m = -15 * m + 16 * m : by ring
  ... = -15 * (8 * a) + 16 * m : by rw [ha]
  ... = -15 * (8 * a) + 16 * (5 * b) : by rw [hb]
  ... = 40 * (-3 * a + 2 * b) : by ring,
end


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n :=
begin
  sorry,
end


example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a :=
begin
  sorry,
end


example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n :=
begin
  sorry,
end


example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n :=
begin
  sorry,
end
