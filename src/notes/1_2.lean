import data.real.basic

/-! # Proving equalities in Lean

We practice writing out calculational proofs in Lean using `calc`, and justifying individual steps
as algebraic manipulation steps (`ring`) or substitution steps (`rw`).

-/

-- Problem 1.1 in notes
example {a b : ℤ} (h1 : a - b = 4) (h2 : a * b = 1) :
  (a + b) ^ 2 = 20 :=
calc (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) : by ring
... = 4 ^ 2 + 4 * 1 : by rw [h1, h2]
... = 20 : by ring

-- Problem 1.2 in notes, replace the `sorry` by the justification
example {r s : ℝ} (h1 : r + 2 * s = -1) (h2 : s = 3) :
  r = -7 :=
calc r = (r + 2 * s) - 2 * s : sorry
... = -1 - 2 * 3 : sorry
... = -7 : sorry

-- Problem 1.3 in notes, translate the whole proof in text to a `calc` proof to Lean
example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
  (2 * a * n + b * m) ^ 2 = 2 :=
sorry

-- Problem 1.4 in notes, translate the whole proof in text to a `calc` proof to Lean
example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
  d * (a * f - b * e) = 0 :=
sorry