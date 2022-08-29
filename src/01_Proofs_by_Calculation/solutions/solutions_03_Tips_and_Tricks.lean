/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.real.basic

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) :
  a = 11 :=
calc a = 2 * b + 5 : by rw [h1]
... = 2 * 3 + 5 : by rw [h2]
... = 11 : by ring

example {x : ℤ} (h1 : x + 4 = 2) : 
  x = -2 :=
calc x = (x + 4) - 4 : by ring
... = 2 - 4 : by rwa [h1]
... = - 2 : by ring

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) :
  a = 9 :=
calc a = (a - 5 * b) + 5 * b : by ring
... = 4 + 5 * b : by rwa [h1]
... = -6 + 5 * (b + 2) : by ring
... = -6 + 5 * 3 : by rwa [h2]
... = 9 : by ring

example {w : ℚ} (h1 : 3 * w + 1 = 4) : 
  w = 1 :=
calc w = (3 * w + 1) / 3 - 1 / 3 : by ring
... = 4 / 3 - 1 / 3 : by rwa [h1]
... = 1 : by ring

example {x : ℤ} (h1 : 2 * x + 3 = x) : 
  x = -3 :=
calc x = (2 * x + 3) - x - 3 : by ring
... = x - x - 3 : by rwa [h1]
... = - 3 : by ring

example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : 
  x = 5 :=
calc x = (2 * x - y) + (y - x + 1) - 1 : by ring
... = 4 + 2 - 1 : by rwa [h1, h2]
... = 5 : by ring

example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) :
  u = 5 :=
calc u = ((u + 2 * v) + (u - 2 * v)) / 2 : by ring
... = (4 + 6) / 2 : by rwa [h1, h2]
... = 5 : by ring

example {a b : ℚ} (h1 : a - 3 = 2 * b) :
  a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
calc a ^ 2 - a + 3 = (a - 3) ^ 2 + 5 * (a - 3) + 9 : by ring
... = (2 * b) ^ 2 + 5 * (2 * b) + 9 : by rwa [h1]
... = 4 * b ^ 2 + 10 * b + 9 : by ring

example {z : ℝ} (h1 : z ^ 2 + 1 = 0) :
  z ^ 4 + z ^ 3 + 2 * z ^ 2 + z + 3 = 2 :=
calc z ^ 4 + z ^ 3 + 2 * z ^ 2 + z + 3
    = z ^ 2 * (z ^ 2 + 1) + z * (z ^ 2 + 1) + (z ^ 2 + 1) + 2 : by ring
... = z ^ 2 * 0 + z * 0 + 0 + 2 : by rwa [h1]
... = 2 : by ring

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) :
  y = 9 :=
calc y = 4 * x - 3 : by rw [h2]
... = 4 * 3 - 3: by rw [h1]
... = 9 : by ring

example {a b : ℤ} (h : a - b = 0) : 
  a = b :=
calc a = (a - b) + b : by ring
... = 0 + b : by rwa [h]
... = b : by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) :
  x = 14 :=
calc x = (x - 3 * y) + 3 * y : by ring
... = 5 + 3 * y : by rwa [h1]
... = 5 + 3 * 3 : by rwa [h2]
... = 14 : by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) :
  p = -1 :=
calc p = (p - 2 * q) + 2 * q : by ring
... = 1 + 2 * q : by rwa [h1]
... = 1 + 2 * (-1) : by rwa [h2]
... = -1 : by ring

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) :
  x = -1 :=
calc x = (x + 2 * y) - 2 * y : by ring
... = 3 - 2 * y : by rwa [h2]
... = 5 - 2 * (y + 1) : by ring
... = 5 - 2 * 3 : by rwa [h1]
... = -1 : by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) :
  p = -11 :=
calc p = (p + 4 * q) - 4 * q : by ring
... = 1 - 4 * q : by rwa [h1]
... = -3 - 4 * (q - 1) : by ring
... = - 3 - 4 * 2 : by rwa [h2]
... = -11 : by ring

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3) (h3 : c = 1) :
  a = 2 :=
calc a = (a + 2 * b + 3 * c) - 2 * b - 3 * c : by ring
... = 7 - 2 * b - 3 * c : by rwa [h1]
... = 7 - 2 * (b + 2 * c) + c : by ring
... = 7 - 2 * 3 + c : by rwa [h2]
... = 1 + c : by ring
... = 1 + 1 : by rwa [h3]
... = 2 : by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) :
  u = 1 / 4 :=
calc u = (4 * u + v) / 4 - v / 4 : by ring
... = 3 / 4 - 2 / 4 : by rwa [h1, h2]
... = 1 / 4 : by ring

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : 
  c = -3 :=
calc c = (4 * c + 1) - 3 * c - 1 : by ring
... = (3 * c - 2) - 3 * c - 1 : by rwa [h1]
... = -3 : by ring

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : 
  p = 2 :=
calc p = ((5 * p - 3) - 3 * p + 3) / 2 : by ring
... = ((3 * p + 1) - 3 * p + 3) / 2 : by rwa [h1]
... = 2 : by ring

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : 
  x = 3 :=
calc x = (2 * x + y) - (x + y) : by ring
... = 4 - 1 : by rwa [h1, h2]
... = 3 : by ring

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : 
  a = 2 :=
calc a = ((a + 2 * b) + 2 * (a - b)) / 3 : by ring
... =  (4 + 2 * 1) / 3 : by rwa [h1, h2]
... = 2 : by ring

example {u v : ℝ} (h1 : u + 1 = v) :
  u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
calc u ^ 2 + 3 * u + 1 = (u + 1) ^ 2 + (u + 1) - 1 : by ring
... = v ^ 2 + v - 1 : by rwa [h1]

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
  t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
calc t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2
  = (t ^ 2 - 4) * (t ^ 2 + 3 * t + 1) + 10 * t + 2 : by ring
... = 0 * (t ^ 2 + 3 * t + 1) + 10 * t + 2 : by rwa [ht]
... = 10 * t + 2 : by ring

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : 
  y = 2 :=
calc y = ((x + 3) * (2 - y) - (2 * x - y * x) + 5 * y - 6) / 2 : by ring
... = (5 * (2 - y) - 0 + 5 * y - 6) / 2 : by rwa [h1, h2]
... = 2 : by ring

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
  p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
calc p ^ 2 + q ^ 2 + r ^ 2 = (p + q + r) ^ 2 - 2 * (p * q + p * r + q * r) : by ring
... = 0 ^ 2 - 2 * 2 : by rwa [h1, h2]
... = -4 : by ring
