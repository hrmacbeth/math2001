/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Take

set_option linter.unusedVariables false
namespace Nat


example (N : ℕ) : ∃ p ≥ N, Prime p := by
  have hN0 : 0 < N ! := by apply factorial_pos
  have hN2 : 2 ≤ N ! + 1 := by addarith [hN0] 
  -- `N! + 1` has a prime factor, `p`
  obtain ⟨p, hp, hpN⟩ : ∃ p : ℕ, Prime p ∧ p ∣ N ! + 1 := exists_prime_factor hN2
  obtain ⟨k, hk⟩ := hpN
  have hp2 : 2 ≤ p
  · obtain ⟨hp', hp''⟩ := hp
    apply hp'
  have hp_pos : 0 < p := by extra
  -- the key fact: `p` is not a factor of `N!`
  have key : ¬ p ∣ (N !)
  · apply Nat.not_dvd_of_exists_lt_and_lt (N !) hp_pos
    have : k ≠ 0 
    · apply ne_of_gt
      apply pos_of_mul_pos_right (a := p)
      · calc 0 < N ! + 1 := by extra
          _ = p * k := hk
      · extra 
    obtain ⟨l, hlk⟩ : ∃ l, k = l + 1 := Nat.exists_eq_succ_of_ne_zero this
    take l
    have hl :=
    calc N ! + 1 = p * k := hk
      _ = p * (l + 1) := by rw [hlk]
    constructor
    · have := 
      calc p * l + p = p * (l + 1) := by ring
        _ = N ! + 1 := by rw [hl]
        _ < N ! + p := by addarith [hp2]
      addarith [this]
    · calc N ! < N ! + 1 := by extra
        _ = p * (l + 1) := by rw [hl]
  -- so `p` is a prime number greater than or equal to `N`, as we sought
  take p
  constructor
  · obtain h_le | h_gt : p ≤ N ∨ N < p := le_or_lt p N
    · have : p ∣ (N !)
      · apply dvd_factorial hp_pos
        addarith [h_le]
      contradiction
    · addarith [h_gt]
  · apply hp 
