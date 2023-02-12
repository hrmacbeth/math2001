import Mathlib.Data.Real.Basic
import Math2001.Library.Prime
import Math2001.Tactic.Numbers
import Math2001.Tactic.Take


def superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)


#numbers 0 ^ 0 ^ 0 + 1 -- 1
#numbers 0 ^ 0 ^ 1 + 1 -- 2
#numbers 0 ^ 0 ^ 2 + 1 -- 2


theorem not_superpowered_zero : ¬ superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  numbers at one_prime -- simplifies that statement to `Prime 1`
  have : ¬ Prime 1 := not_prime_one
  contradiction


#numbers 1 ^ 1 ^ 0 + 1 -- 2
#numbers 1 ^ 1 ^ 1 + 1 -- 2
#numbers 1 ^ 1 ^ 2 + 1 -- 2


theorem superpowered_one : superpowered 1 := by
  intro n
  ring_nf -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two


#numbers 2 ^ 2 ^ 0 + 1 -- 3
#numbers 2 ^ 2 ^ 1 + 1 -- 5
#numbers 2 ^ 2 ^ 2 + 1 -- 17
#numbers 2 ^ 2 ^ 3 + 1 -- 257
#numbers 2 ^ 2 ^ 4 + 1 -- 65537


#numbers 3 ^ 3 ^ 0 + 1 -- 4
#numbers 3 ^ 3 ^ 1 + 1 -- 28
#numbers 3 ^ 3 ^ 2 + 1 -- 19684


theorem not_superpowered_three : ¬(superpowered 3) := by
  intro h
  dsimp [superpowered] at h
  have four_prime : Prime (3 ^ 3 ^ 0 + 1) := h 0
  numbers at four_prime -- simplifies that statement to `Prime 4`
  have four_not_prime : ¬(Prime 4)
  · apply not_prime 2
    · numbers -- show `2 ≠ 1` 
    · numbers -- show `2 ≠ 4` 
    take 2
    numbers -- show `4 = 2 * 2`
  contradiction


example : ∃ k : ℕ, superpowered k ∧ ¬ superpowered (k + 1) := by
  by_cases h2 : superpowered 2
  · take 2
    constructor
    · apply h2
    · apply not_superpowered_three
  · take 1
    constructor
    · apply superpowered_one
    · apply h2      


def tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

example : ∃ x : ℝ, tribalanced x ∧ ¬ tribalanced (x + 1) := by
  sorry

example : ∃ k : ℕ, superpowered k ∧ ¬ superpowered (k + 1) := by
  sorry
