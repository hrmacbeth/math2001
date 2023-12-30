/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.InjectiveSurjective
import Library.Basic
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function



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
  use (0, 1)
  intro m hm
  dsimp [q] at hm
  obtain ⟨hm1, hm2⟩ := hm
  have H : 1 = -1 := by addarith [hm1, hm2]
  numbers at H


example : Bijective (fun ((m, n) : ℤ × ℤ) ↦ (m + n, m + 2 * n)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a, b) ↦ (2 * a - b, b - a)
  constructor
  · ext ⟨m, n⟩
    dsimp
    ring
  · ext ⟨a, b⟩
    dsimp
    ring


example : Bijective (fun ((m, n) : ℝ × ℝ) ↦ (m + n, m - n)) := by
  sorry

example : ¬ Bijective (fun ((m, n) : ℤ × ℤ) ↦ (m + n, m - n)) := by
  dsimp [Bijective, Injective, Surjective]
  push_neg
  right
  use (0, 1)
  intro (m, n) h
  dsimp at h
  obtain ⟨h1, h2⟩ := h
  have :=
  calc 0 ≡ 2 * m [ZMOD 2] := by extra
    _ = (m - n) + (m + n) := by ring
    _ = 1 + 0 := by rw [h1, h2]
    _ = 1 := by numbers
  numbers at this


example : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x - y, y)) := by
  intro (x1, y1) (x2, y2) h
  dsimp at h
  obtain ⟨h, h', hy⟩ := h
  constructor
  · addarith [h, hy]
  · apply hy


example : ¬ Injective (fun ((x, y) : ℝ × ℝ) ↦ x + y) := by
  dsimp [Injective]
  push_neg
  use (0, 0), (1, -1)
  dsimp
  constructor
  · numbers
  · numbers

example : Surjective (fun ((x, y) : ℝ × ℝ) ↦ x + y) := by
  intro a
  use (a, 0)
  dsimp
  ring


example : ¬ Injective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 8 * n) := by
  dsimp [Injective]
  push_neg
  use (0, 0), (8, -5)
  constructor
  · numbers
  · numbers

example : Surjective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 8 * n) := by
  intro a
  use (-3 * a, 2 * a)
  dsimp
  ring


example : ¬ Injective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 10 * n) := by
  sorry

example : ¬ Surjective (fun ((m, n) : ℤ × ℤ) ↦ 5 * m + 10 * n) := by
  dsimp [Surjective]
  push_neg
  use 1
  intro (m, n) h
  dsimp at h
  have :=
  calc 0 ≡ 5 * (m + 2 * n) [ZMOD 5] := by extra
    _ = 5 * m + 10 * n := by ring
    _ = 1 := h
  numbers at this


def g : ℝ × ℝ → ℝ × ℝ
  | (x, y) => (y, x)

example : g ∘ g = id := by
  ext ⟨x, y⟩
  dsimp [g]


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


def p : ℕ × ℕ → ℕ
  | (a, b) => A (a + b) + b


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
    · zify at hab ⊢
      calc (b1:ℤ) = A (a2 + b2) + b2 - A (a1 + b1) := by addarith [hab]
        _ = A (a2 + b2) + b2 - A (a2 + b2) := by rw [H]
        _ = b2 := by ring
    constructor
    · zify at hb H ⊢
      addarith [H, hb]
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

example : Surjective (fun ((a, b) : ℚ × ℕ) ↦ a ^ b) := by
  sorry

example : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by
  sorry

example : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by
  sorry

def h : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | (x, y, z) => (y, z, x)

example : h ∘ h ∘ h = id := by
  sorry
