/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init
set_option pp.funBinderTypes true

open Function


def f (a : ℝ) : ℝ := a + 3
def g (b : ℝ) : ℝ := 2 * b
def h (c : ℝ) : ℝ := 2 * c + 6

example : g ∘ f = h := by
  ext x
  calc (g ∘ f) x = g (f x) := by rfl
    _ = 2 * (x + 3) := by rfl
    _ = 2 * x + 6 := by ring
    _ = h x := by rfl


def s (x : ℝ) : ℝ := 5 - x

example : s ∘ s = id := by
  ext x
  dsimp [s]
  ring


def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id


inductive Humour
  | melancholic
  | choleric
  | phlegmatic
  | sanguine
  deriving DecidableEq

open Humour


def p : Humour → Humour
  | melancholic => choleric
  | choleric => sanguine
  | phlegmatic => phlegmatic
  | sanguine => melancholic


def q : Humour → Humour
  | melancholic => sanguine
  | choleric => melancholic
  | phlegmatic => phlegmatic
  | sanguine => choleric

example : Inverse p q := by
  constructor
  · ext x
    cases x <;> exhaust
  · ext x
    cases x <;> exhaust


theorem exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨h_inj, h_surj⟩ := hf
  dsimp [Surjective] at h_surj
  choose g hg using h_surj
  use g
  dsimp [Inverse]
  constructor
  · -- prove `g ∘ f = id`
    ext x
    dsimp [Injective] at h_inj
    apply h_inj
    calc f ((g ∘ f) x) = f (g (f x)) := by rfl
      _ = f x := by apply hg
      _ = f (id x) := by rfl
  · -- prove `f ∘ g = id`
    ext y
    apply hg


theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by rfl
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rfl
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rfl
      _ = id x2 := by rw [hgf]
      _ = x2 := by rfl
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rfl
      _ = id y := by rw [hfg]
      _ = y := by rfl


theorem bijective_iff_exists_inverse (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g := by
  constructor
  · apply exists_inverse_of_bijective
  · intro h
    obtain ⟨g, H⟩ := h
    apply bijective_of_inverse H


/-! # Exercises -/


def a : Humour → Humour
  | melancholic => sanguine
  | choleric => choleric
  | phlegmatic => phlegmatic
  | sanguine => melancholic

def b : Humour → Humour
  | melancholic => phlegmatic
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => sanguine

def c : Humour → Humour
  | melancholic => sorry
  | choleric => sorry
  | phlegmatic => sorry
  | sanguine => sorry

example : b ∘ a = c := by
  ext x
  cases x <;> exhaust


def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := sorry

example : Inverse u v := by
  sorry

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  sorry

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  sorry

example {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  sorry

example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  sorry
