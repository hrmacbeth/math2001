import data.real.basic

/-! # Tips and tricks -/

/-! ## Problems from notes -/

-- Problem 1.5 in text
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) :
  a = 11 :=
calc a = 2 * b + 5 : by rw [h1]
... = 2 * 3 + 5 : by rw [h2]
... = 11 : by ring

-- Problem 1.6 in text
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
calc x = (x + 4) - 4 : by ring
... = 2 - 4 : by rw [h1]
... = - 2 : by ring

-- Problem 1.7 in text
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) :
  a = 9 :=
calc a = (a - 5 * b) + 5 * b : by ring
... = 4 + 5 * b : by rw [h1]
... = -6 + 5 * (b + 2) : by ring
... = -6 + 5 * 3 : by rw [h2]
... = 9 : by ring

-- Problem 1.8 in text
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
calc w = (3 * w + 1) / 3 - 1 / 3 : by ring
... = 4 / 3 - 1 / 3 : by rw [h1]
... = 1 : by ring

-- Problem 1.9 in text
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
calc x = (2 * x + 3) - x - 3 : by ring
... = x - x - 3 : by rw [h1]
... = - 3 : by ring

-- Problem 1.10 in text
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
calc x = (2 * x - y) + (y - x + 1) - 1 : by ring
... = 4 + 2 - 1 : by rw [h1, h2]
... = 5 : by ring

-- Problem 1.11 in text
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) :
  u = 5 :=
calc u = ((u + 2 * v) + (u - 2 * v)) / 2 : by ring
... = (4 + 6) / 2 : by rw [h1, h2]
... = 5 : by ring

-- Problem 1.12 in text
example {a b : ℚ} (h1 : a - 3 = 2 * b) :
  a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
calc a ^ 2 - a + 3 = (a - 3) ^ 2 + 5 * (a - 3) + 9 : by ring
... = (2 * b) ^ 2 + 5 * (2 * b) + 9 : by rw [h1]
... = 4 * b ^ 2 + 10 * b + 9 : by ring

-- Problem 1.13 in text, but for complex numbers
example {z : ℝ} (h1 : z ^ 2 + 1 = 0) : z ^ 4 + z ^ 3 + 2 * z ^ 2 + z + 3 = 2 :=
calc z ^ 4 + z ^ 3 + 2 * z ^ 2 + z + 3
    = z ^ 2 * (z ^ 2 + 1) + z * (z ^ 2 + 1) + (z ^ 2 + 1) + 2 : by ring
... = z ^ 2 * 0 + z * 0 + 0 + 2 : by rw [h1]
... = 2 : by ring

/-! ## Exercises -/

-- exercise 1
example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) :
  y = 9 :=
sorry

-- exercise 2
example {a b : ℤ} (h : a - b = 0) : a = b :=
sorry

-- exercise 3
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) :
  x = 14 :=
sorry

-- exercise 4
example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) :
  p = -1 :=
sorry

-- exercise 5
example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) :
  x = -1 :=
sorry

-- exercise 6
example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) :
  p = -11 :=
sorry

-- exercise 7
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3) (h3 : c = 1) :
  a = 2 :=
sorry

-- exercise 8
example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) :
  u = 1 / 4 :=
sorry

-- exercise 9
example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
sorry

-- exercise 10
example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
sorry

-- exercise 11
example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
sorry

-- exercise 12
example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
sorry

-- exercise 13
example {u v : ℝ} (h1 : u + 1 = v) :
  u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
sorry

-- exercise 14
example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
  t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
sorry

-- exercise 15
example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
sorry

-- exercise 16
example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
  p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
sorry