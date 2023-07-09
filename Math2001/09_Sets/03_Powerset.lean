import Library.Tactic.Define
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Extra
import Library.Tactic.Induction
import Library.Tactic.Numbers
import Library.Tactic.Use
import Library.Theory.Parity

set_option push_neg.use_distrib true
open Set

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
attribute [-simp] Set.setOf_eq_eq_singleton

macro_rules | `(conv | ring) => `(conv | ring_nf)

open Function


#check {3, 4, 5} -- `{3, 4, 5} : Set ℕ`
#check {n : ℕ | 8 < n} -- `{n | 8 < n} : Set ℕ`
#check {k : ℕ | ∃ a, a ^ 2 = k} -- `{k | ∃ a, a ^ 2 = k} : Set ℕ`


#check {{3, 4}, {4, 5, 6}} -- `{{3, 4}, {4, 5, 6}} : Set (Set ℕ)`
#check {s : Set ℕ | 3 ∈ s} -- `{s | 3 ∈ s} : Set (Set ℕ)`



example : {n : ℕ | Nat.Even n} ∉ {s : Set ℕ | 3 ∈ s} := by
  dsimp
  rw [← Nat.odd_iff_not_even]
  use 1
  numbers


def p (s : Set ℕ) : Set ℕ := {n : ℕ | n + 1 ∈ s}

#check @p -- `p : Set ℕ → Set ℕ`


example : ¬ Injective p := by
  dsimp [Injective, p]
  push_neg
  use {0}, ∅
  dsimp
  constructor
  · intro x
    apply ne_of_gt
    extra
  · use 0
    numbers


def q (s : Set ℤ) : Set ℤ := {n : ℤ | n + 1 ∈ s}

example : Injective q := by
  dsimp [Injective, q]
  intro s t hst n
  have hn : (n - 1) + 1 ∈ s ↔ (n - 1) + 1 ∈ t := hst (n - 1)
  conv at hn => ring
  apply hn



example : ¬ ∃ f : X → Set X, Surjective f := by
  intro h
  obtain ⟨f, hf⟩ := h
  let s : Set X := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := hf s
  by_cases hxs : x ∈ s
  · have hfx : x ∉ f x := hxs
    rw [hx] at hfx
    contradiction
  · have hfx : ¬ x ∉ f x := hxs
    rw [hx] at hfx
    contradiction

/-! # Exercises -/


def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  sorry

namespace Int

def U : ℕ → Set ℤ 
  | 0 => univ
  | n + 1 => {x : ℤ | ∃ y ∈ U n, x = 2 * y}

example (n : ℕ) : U n = {x : ℤ | (2:ℤ) ^ n ∣ x} := by
  simple_induction n with k hk
  · rw [U]
    dsimp
    sorry
  · rw [U]
    dsimp at *
    sorry
