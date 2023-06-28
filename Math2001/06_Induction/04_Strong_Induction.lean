/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Induction
import Library.Tactic.Numbers
import Library.Tactic.Take

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
set_option push_neg.use_distrib true
set_option linter.unusedVariables false
open Nat


def d : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | k + 2 => 3 * d (k + 1) + 5 * d k

theorem d_bound (n : ℕ) (hn : n ≥ 4) : d n ≥ 4 ^ n := by
  obtain h | h := lt_or_le n 6
  · -- Case 1: `n < 6`
    interval_cases n
    · -- if `n = 4`
      calc d 4 = 267 := by rfl
        _ ≥ 4 ^ 4 := by numbers
    · -- if `n = 5`
      calc d 5 = 1096 := by rfl
        _ ≥ 4 ^ 5 := by numbers
  · -- Case 2: `6 ≤ n`
    have H : ∃ k, n = k + 2
    · apply Nat.exists_eq_add_of_le'
      addarith [h]
    obtain ⟨k, hk⟩ := H
    have IH1 : d k ≥ 4 ^ k
    · apply d_bound k -- first inductive hypothesis
      addarith [hk, h]
    have IH2 : d (k + 1) ≥ 4 ^ (k + 1) -- second inductive hypothesis
    · apply d_bound (k + 1)
      addarith [hk, h]
    have H : (17:ℤ) ≥ 16 := by numbers
    calc d n = d (k + 2) := by rw [hk]
      _ = 3 * d (k + 1) + 5 * d k := by rw [d]
      _ ≥ 3 * 4 ^ (k + 1) + 5 * 4 ^ k := by rel [IH1, IH2]
      _ = 17 * 4 ^ k := by ring
      _ ≥ 16 * 4 ^ k := by rel [H] 
      _ = 4 ^ (k + 2) := by ring
      _ = 4 ^ n := by rw [hk]

example : forall_sufficiently_large n : ℕ, d n ≥ 4 ^ n := by
  dsimp
  take 4
  apply d_bound


namespace Nat

theorem exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  by_cases hn : Prime n 
  . -- case 1: `n` is prime
    take n
    constructor
    · apply hn
    · take 1
      ring
  . -- case 2: `n` is not prime
    obtain ⟨m, hmn, _, ⟨x, hx⟩⟩ := exists_factor_of_not_prime hn hn2
    have IH : ∃ p, Prime p ∧ p ∣ m := exists_prime_factor hmn -- inductive hypothesis
    obtain ⟨p, hp, y, hy⟩ := IH
    take p
    constructor
    · apply hp
    · take x * y
      calc n = m * x := hx
        _ = (p * y) * x := by rw [hy]
        _ = p * (x * y) := by ring

/-! # Exercises -/


theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  sorry
