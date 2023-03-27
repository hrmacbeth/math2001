/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option pp.unicode.fun true
set_option linter.unusedVariables false


def F : ℕ → ℤ 
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n 

#eval F 5 -- infoview displays `8`  


#check @F -- infoview displays `F : ℕ → ℤ`  


def q (x : ℝ) : ℝ := x + 3


#check @q -- infoview displays `q : ℝ → ℝ`  


#check fun (x : ℝ) ↦ x ^ 2 -- infoview displays `fun x ↦ x ^ 2 : ℝ → ℝ`  


def Injective (f : X → Y) : Prop := ∀ x1 x2 : X, f x1 = f x2 → x1 = x2


example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  addarith [h]


example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  take -1, 1
  constructor
  · numbers
  · numbers  


def Surjective (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, f x = y


def s (a : ℚ) : ℚ := 3 * a + 2

example : Surjective s := by
  dsimp [Surjective]
  intro y
  take (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
    _ = y := by ring


example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  take -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by numbers
    _ ≤ x ^ 2 := by extra


inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer


def f : Musketeer → Musketeer
  | athos => aramis
  | porthos => aramis
  | aramis => athos


example : ¬ Injective f := by
  dsimp [Injective]
  push_neg
  take athos, porthos
  dsimp [f]
  constructor
  · decide
  · decide


example : ¬ Surjective f := by
  dsimp [Surjective]
  push_neg
  take porthos
  intro a
  cases a <;> dsimp [f]
  · decide
  · decide
  · decide


def g : Musketeer → Musketeer
  | athos => porthos
  | porthos => aramis
  | aramis => athos


example : Injective g := by
  dsimp [Injective]
  intro x1 x2 hx
  cases x1 <;> cases x2 <;> dsimp [g] at hx
  · trivial
  · contradiction
  · contradiction
  · contradiction
  · decide
  · contradiction
  · contradiction
  · contradiction
  · decide


example : Surjective g := by
  dsimp [Surjective]
  intro y
  cases y
  · take aramis
    decide
  · take athos
    decide
  · take porthos
    decide 

/-! # Exercises -/


example : Injective (fun (x : ℚ) ↦ x - 12) := by
  sorry

example : ¬ Injective (fun (x : ℚ) ↦ x - 12) := by
  sorry


example : Injective (fun (x : ℝ) ↦ 0) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 0) := by
  sorry

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry

example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry


example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry

example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry


example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry

example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry


example : Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by
  sorry

example : Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  sorry

example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by
  sorry

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  sorry

example : ∀ (f : ℚ → ℚ) (hf : Injective f), Injective (fun x ↦ f x + 1) := by
  sorry

example : ¬ ∀ (f : ℚ → ℚ) (hf : Injective f), Injective (fun x ↦ f x + 1) := by
  sorry


example : ∀ (f : ℚ → ℚ) (hf : Injective f), Injective (fun x ↦ f x + x) := by
  sorry

example : ¬ ∀ (f : ℚ → ℚ) (hf : Injective f), Injective (fun x ↦ f x + x) := by
  sorry

example : ∀ (f : ℤ → ℤ) (hf : Surjective f), Surjective (fun x ↦ 2 * f x) := by
  sorry

example : ¬ ∀ (f : ℤ → ℤ) (hf : Surjective f), Surjective (fun x ↦ 2 * f x) := by
  sorry
