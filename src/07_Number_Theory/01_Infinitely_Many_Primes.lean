/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Math2001.Library.Prime
import Math2001.Tactic.Addarith
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option linter.unusedVariables false
open Nat


example (N : ℕ) : ∃ p ≥ N, Prime p := by
  have hN0 : 0 < N ! := by apply factorial_pos
  have hN2 : 2 ≤ N ! + 1 := by addarith [hN0] 
  obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, Prime p ∧ p ∣ N ! + 1 := exists_prime_factor hN2
  take p
  constructor
  · obtain h_le | h_ge : N ≤ p ∨ p < N := le_or_lt N p
    · apply h_le
    have hp2 : 2 ≤ p
    · obtain ⟨hp', hp''⟩ := hp
      apply hp'
    have hp_pos : 0 < p := by extra
    have h_dvd : p ∣ (N !)
    · apply dvd_factorial hp_pos
      addarith [h_ge]
    obtain ⟨k, hk⟩ := h_dvd
    have : ¬ p ∣ (N ! + 1)
    · apply Nat.not_dvd_of_exists_lt_and_lt (N ! + 1) hp_pos
      take k
      constructor
      · addarith [hk]
      calc N ! + 1 = p * k + 1 := by addarith [hk]
        _ < p * k + p := by addarith [hp2]
        _ = p * (k + 1) := by ring
    contradiction
  · apply hp 
