/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Tactic.Addarith
import Math2001.Tactic.ExistsDelaborator
import Math2001.Tactic.Induction
import Math2001.Tactic.ModCases
import Math2001.Tactic.Numbers
import Math2001.Tactic.Product
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option linter.unusedVariables false
set_option push_neg.use_distrib true
attribute [-simp] ne_eq
open Function

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id
theorem bijective_iff_exists_inverse (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g :=
  sorry

/-! # Product types -/


def q (m : ℤ) : ℤ × ℤ := (m + 1, 2 - m)

example : Injective q := by
  dsimp [Injective]
  intro m1 m2 hm
  dsimp [q] at hm
  obtain ⟨hm', hm''⟩ := hm
  addarith [hm']

example : ¬ Surjective q := by
  dsimp [Surjective]
  push_neg
  take (0, 1)
  intro a ha
  dsimp [q] at ha
  obtain ⟨ha1, ha2⟩ := ha
  have H : 0 = -1 := by addarith [ha1, ha2]
  numbers at H


example : Bijective (fun ((m, n) : ℤ × ℤ) ↦ (m + n, m + 2 * n)) := by
  rw [bijective_iff_exists_inverse]
  take fun (a, b) ↦ (2 * a - b, b - a)
  constructor
  · funext x
    let (m, n) := x
    dsimp
    constructor
    · ring
    · ring 
  · funext x
    let (a, b) := x
    dsimp
    constructor
    · ring
    · ring 


example : Bijective (fun ((m, n) : ℝ × ℝ) ↦ (m + n, m - n)) := by
  sorry

example : ¬ Bijective (fun ((m, n) : ℤ × ℤ) ↦ (m + n, m - n)) := by
  dsimp [Bijective, Injective, Surjective]
  push_neg
  right
  take (0, 1)
  intro (m, n) h
  dsimp at h
  obtain ⟨h1, h2⟩ := h
  have :=
  calc 0 ≡ 2 * m [ZMOD 2] := by extra
    _ = (m - n) + (m + n) := by ring
    _ = 1 + 0 := by rw [h1, h2]
    _ = 1 := by numbers
  numbers at this


example : ¬ Injective (fun ((x, y) : ℝ × ℝ) ↦ x + y) := by
  dsimp [Injective]
  push_neg
  take (0, 0), (1, -1)
  dsimp
  constructor
  · numbers
  · intro h
    obtain ⟨h1, h2⟩ := h
    numbers at h1
    
example : Surjective (fun ((x, y) : ℝ × ℝ) ↦ x + y) := by
  intro a
  take (a, 0)
  dsimp
  ring


example : ¬ Injective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 7 * n) := by
  dsimp [Injective]
  push_neg
  take (0, 0), (7, -5)
  constructor
  · numbers
  · intro h
    obtain ⟨h1, h2⟩ := h
    numbers at h1

example : Surjective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 7 * n) := by
  intro a
  take (3 * a, -2 * a)
  dsimp
  ring


example : ¬ Injective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 10 * n) := by
  dsimp [Injective]
  push_neg
  take (0, 0), (10, -5)
  constructor
  · numbers
  · intro h
    obtain ⟨h1, h2⟩ := h
    numbers at h1

example : ¬ Surjective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 10 * n) := by
  dsimp [Surjective]
  push_neg
  take 1
  intro (m, n) h
  dsimp at h
  have :=
  calc 0 ≡ 5 * (m + 2 * n) [ZMOD 5] := by extra
    _ = 5 * m + 10 * n := by ring
    _ = 1 := h
  numbers at this


def g (v : ℝ × ℝ) : ℝ × ℝ :=
  let (x, y) := v
  (-y, x)

example : g ∘ g = - id := by
  funext v
  let (x, y) := v
  dsimp [g]
  constructor
  · ring
  · ring


def A : ℕ → ℕ
  | 0 => 0
  | n + 1 => A n + n + 1

theorem A_mono {n m : ℕ} (h : n ≤ m) : A n ≤ A m := by
  induction_from_starting_point m, h with k hk IH
  · extra
  · calc A n ≤ A k := IH
      _ ≤ A k + (k + 1) := by extra
      _ = A k + k + 1 := by ring
      _ = A (k + 1) := by rw [A]

-- STUDENTS: ignore this, it is temporary while waiting for a bugfix
theorem s_zero : A 0 = 0 := rfl
theorem s_succ (n : ℕ) : A (n + 1) = A n + n + 1 := rfl

-- ignore this too
open Lean Meta in
#eval modifyEnv (m := MetaM) fun env =>
  eqnsExt.modifyState env fun s =>
    { s with map := s.map.insert ``A #[``s_succ, ``s_zero] }


theorem of_A_add_mono {a1 a2 b1 b2 : ℕ} (h : A (a1 + b1) + b1 ≤ A (a2 + b2) + b2) :
    a1 + b1 ≤ a2 + b2 := by
  obtain h' | h' : _ ∨ a2 + b2 + 1 ≤ a1 + b1 := le_or_lt (a1 + b1) (a2 + b2)
  · apply h'
  rw [← not_lt] at h
  have :=
  calc A (a2 + b2) + b2
     < A (a2 + b2) + b2 + (a2 + 1) := by extra
    _ = A (a2 + b2) + (a2 + b2) + 1 := by ring
    _ = A ((a2 + b2) + 1) := by rw [A]
    _ = A (a2 + b2 + 1) := by ring
    _ ≤ A (a1 + b1) := A_mono h'
    _ ≤ A (a1 + b1) + b1 := by extra
  contradiction


def p (x : ℕ × ℕ) : ℕ :=
  let (a, b) := x
  A (a + b) + b


def i : ℕ × ℕ → ℕ × ℕ
  | (0, b) => (b + 1, 0)
  | (a + 1, b) => (a, b + 1)

theorem p_comp_i (x : ℕ × ℕ) : p (i x) = p x + 1 := by
  match x with
  | (0, b) =>
    calc p (i (0, b)) = p (b + 1, 0) := by rw [i]
      _ = A ((b + 1) + 0) + 0 := by dsimp [p]
      _ = A (b + 1) := by ring
      _ = A b + b + 1 := by rw [A]
      _ = (A (0 + b) + b) + 1 := by ring
      _ = p (0, b) + 1 := by dsimp [p]
  | (a + 1, b) =>
    calc p (i (a + 1, b)) = p (a, b + 1) := by rw [i] ; rfl -- FIXME
      _ = A (a + (b + 1)) + (b + 1) := by dsimp [p]
      _ = (A ((a + 1) + b) + b) + 1 := by ring
      _ = p (a + 1, b) + 1 := by rw [p]

example : Bijective p := by
  constructor
  · intro (a1, b1) (a2, b2) hab
    dsimp [p] at hab
    have H : a1 + b1 = a2 + b2
    · apply le_antisymm
      · apply of_A_add_mono
        rw [hab]
      · apply of_A_add_mono
        rw [hab]
    have hb : b1 = b2
    · apply add_left_cancel (a := A (a1 + b1))
      calc A (a1 + b1) + b1 = A (a2 + b2) + b2 := by rw [hab]
        _ = A (a1 + b1) + b2 := by rw [H]
    constructor
    · apply add_right_cancel (b := b1)
      calc a1 + b1 = a2 + b2 := H
        _ = a2 + b1 := by rw [hb]
    · apply hb
  · apply surjective_of_intertwining (x0 := (0, 0)) (i := i)
    · calc p (0, 0) = A (0 + 0) + 0 := by dsimp [p]
        _ = A 0 := by ring
        _ = 0 := by rw [A]
    · intro x
      apply p_comp_i

/-! # Exercises -/


example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  sorry

example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  sorry
example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  sorry

example : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by
  sorry

example : Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 - y ^ 2) := by
  sorry

def h (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (x, y, z) := v
  (y, z, x)

example : h ∘ h ∘ h = id := by
  sorry
