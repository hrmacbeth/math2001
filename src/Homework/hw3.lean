/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Math2001.Library.Parity
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

/-! # Homework 3 -/

open Int


/- 4 points -/
theorem problem1 {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  sorry

/- 5 points -/
theorem problem2 (n : ℤ) : Odd (5 * n ^ 2 + 3 * n + 7) := by
  sorry

/- 4 points -/
theorem problem3 : ¬(3 : ℤ) ∣ -10 := by
  sorry

/- 4 points -/
theorem problem4 {a b c : ℤ} (hab : a ^ 2 ∣ b) (hbc : b ^ 3 ∣ c) : a ^ 6 ∣ c := by
  sorry

/- 4 points -/
theorem problem5 (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  sorry

/- 4 points -/
theorem problem6 {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  sorry
