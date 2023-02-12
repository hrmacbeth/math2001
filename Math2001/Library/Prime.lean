/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.IntervalCases
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

lemma not_prime_one : ¬ Prime 1 := by
  rintro ⟨h, _⟩
  norm_num1 at h

lemma prime_two : Prime 2 := by
  apply prime_test
  · norm_num
  intro m hm1 hm2
  interval_cases m

lemma not_prime {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬(Prime p) := by
  rintro ⟨_, hfact⟩
  obtain hk1' | hkp' := hfact k hk
  · exact hk1 hk1'
  · exact hkp hkp'
