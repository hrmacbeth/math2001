/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.Positivity

def Prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

theorem prime_test {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  refine ⟨hp, fun m hmp => ?_⟩
  have hp' : 0 < p := by positivity
  obtain hm | hm_left := eq_or_lt_of_le (id (Nat.pos_of_dvd_of_pos hmp hp') : 1 ≤ m)
  · left
    exact hm.symm
  obtain hm' | hm_right := eq_or_lt_of_le (Nat.le_of_dvd hp' hmp)
  · right
    exact hm'
  have : ¬m ∣ p := H m hm_left hm_right
  contradiction