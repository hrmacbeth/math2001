/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic
import tactics.inequalities

example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : 
  x + y < 2 :=
calc x + y ≤ x + (x + 5) : by ineq_tac [h1]
... = 2 * x + 5 : by ring
... ≤ 2 * -2 + 5 : by ineq_tac [h2]
... = 1 : by ring
... < 2 : by norm_num

example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B) (h5 : y ≤ B)
(h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
  u * y + v * x + u * v < 3 * A * B :=
calc u * y + v * x + u * v
  ≤ u * B + v * B + u * v : by ineq_tac [h5, h4]
... ≤ A * B + A * B + A * v : by ineq_tac [h8, h9]
... ≤ A * B + A * B + 1 * v : by ineq_tac [h2]
... ≤ A * B + A * B + B * v : by ineq_tac [h3]
... < A * B + A * B + B * A : by ineq_tac [h9]
... = 3 * A * B : by ring

example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
calc (x + y) ^ 2 = (x + y) ^ 2 + 0 : by ring
... ≤ (x + y) ^ 2 + (x - y) ^ 2 : by ineq_tac []
... = 2 * (x ^ 2 + y ^ 2) : by ring
... ≤ 2 * 1 : by ineq_tac [h]
... < 3 : by norm_num

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
calc a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * a * b : by ring
... ≥ 0 + 2 * a * b : by ineq_tac []
... = 2 * a * b : by ring


example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : 
  a + b ≥ 3 :=
calc a + b = ((a + 2 * b) + a) / 2 : by ring
... ≥ (4 + 3) / 2 : by ineq_tac [h1, h2]
... ≥ 3 : by norm_num

example {x : ℤ} (hx : x ≥ 9) : 
  x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
calc x ^ 3 - 8 * x ^ 2 + 2 * x
  = x * x ^ 2 - 8 * x ^ 2 + 2 * x : by ring
... ≥ 9 * x ^ 2 - 8 * x ^ 2 + 2 * x : by ineq_tac [hx]
... = x ^ 2 + 2 * x : by ring
... ≥ 9 ^ 2 + 2 * 9 : by ineq_tac [hx]
... ≥ 3 : by norm_num

example {n : ℤ} (hn : n ≥ 10) : 
  n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
calc n ^ 4 - 2 * n ^ 2
  = n * n ^ 3 - 2 * n ^ 2 : by ring
... ≥ 10 * n ^ 3 - 2 * n ^ 2 :  by ineq_tac [hn]
... = 3 * n ^ 3 + 7 * n * n ^ 2 - 2 * n ^ 2 : by ring
... ≥ 3 * n ^ 3 + 7 * 10 * n ^ 2 - 2 * n ^ 2 : by ineq_tac [hn]
... = 3 * n ^ 3 + 68 * n ^ 2 : by ring
... > 3 * n ^ 3 + 0 : by ineq_tac []
... = 3 * n ^ 3 : by ring

example {n : ℤ} (h1 : n ≥ 5) :
  n ^ 2 - 2 * n + 3 > 14 :=
calc n ^ 2 - 2 * n + 3 = n * n - 2 * n + 3 : by ring
... ≥ 5 * n - 2 * n + 3 : by ineq_tac [h1]
... = 3 * n + 3 : by ring
... ≥ 3 * 5 + 3 : by ineq_tac [h1]
... > 14 : by norm_num

example {x : ℚ} :
  x ^ 2 - 2 * x ≥ -1 :=
calc x ^ 2 - 2 * x = (x - 1) ^ 2 - 1 : by ring
... ≥ 0 - 1 : by ineq_tac []
... = -1 : by ring

