/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/


-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  sorry

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  sorry

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  sorry

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  sorry

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  sorry

-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  sorry

-- Example 1.3.7
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  sorry

-- Example 1.3.8
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  sorry

-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  sorry

-- Example 1.3.10
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  sorry

/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  sorry

example {a b : ℤ} (h : a - b = 0) : a = b :=
  sorry

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  sorry

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  sorry

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  sorry

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  sorry

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  sorry

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  sorry

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  sorry

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  sorry

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  sorry

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  sorry

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  sorry

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  sorry

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  sorry

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  sorry
