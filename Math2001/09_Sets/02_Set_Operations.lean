/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.ParityModular
import Library.Tactic.Addarith
import Library.Tactic.Define
import Library.Tactic.ModCases
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

set_option push_neg.use_distrib true
open Set

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
attribute [-simp] Set.setOf_eq_eq_singleton



example (t : ℝ) : t ∈ {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} := by
  dsimp
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp
  intro t h
  obtain ⟨(h1 | h1), h2⟩ := h
  · have :=
    calc (-2) ^ 2 = t ^ 2 := by rw [h1]
      _ = 9 := by rw [h2]
    numbers at this
  · addarith [h1]


namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  dsimp
  intro n
  rw [odd_iff_not_even]
end Int


example (x : ℤ) : x ∉ ∅ := by dsimp

example (U : Set ℤ) : ∅ ⊆ U := by dsimp


example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  dsimp
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have :=
  calc 1 ≡ x [ZMOD 5] := by rel [hx1]
    _ ≡ 2 [ZMOD 5] := by rel [hx2]
  numbers at this


example (x : ℤ) : x ∈ univ := by dsimp

example (U : Set ℤ) : U ⊆ univ := by dsimp


example : {x : ℝ | -1 < x} ∪ {x : ℝ | x < 1} = univ := by
  dsimp
  intro t
  obtain h | h := le_or_lt t 0
  · right
    addarith [h]
  · left
    addarith [h]


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  dsimp
  intro n
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
    · right
      left
      apply h
    · right
      right
      apply h
  · intro h
    sorry -- can't be bothered typing out the rest


example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by aesop



example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp
  intro n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> aesop


/-! # Exercises -/


example : {-1, 2, 4, 4} ∪ {3, -2, 2} = sorry := by aesop

example : {0, 1, 2, 3, 4} ∩ {0, 2, 4, 6, 8} = sorry := by aesop

example : {1, 2} ∩ {3} = sorry := by aesop

example : {3, 4, 5}ᶜ ∩ {1, 3, 5, 7, 9} = sorry := by aesop

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  sorry

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  sorry

example :
    {n : ℤ | 3 ∣ n} ∪ {n : ℤ | 2 ∣ n} ⊆ {n : ℤ | n ^ 2 ≡ 1 [ZMOD 6]}ᶜ := by
  sorry

def SizeAtLeastTwo (s : Set X) : Prop := ∃ x1 x2 : X, x1 ≠ x2 ∧ x1 ∈ s ∧ x2 ∈ s 
def SizeAtLeastThree (s : Set X) : Prop :=
  ∃ x1 x2 x3 : X, x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 ∧ x1 ∈ s ∧ x2 ∈ s ∧ x3 ∈ s 

example {s t : Set X} (hs : SizeAtLeastTwo s) (ht : SizeAtLeastTwo t)
    (hst : ¬ SizeAtLeastTwo (s ∩ t)) :
    SizeAtLeastThree (s ∪ t) := by
  sorry
