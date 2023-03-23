/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Math2001.Library.Prime
import Math2001.Tactic.Addarith
import Math2001.Tactic.Induction
import Math2001.Tactic.Take
import Mathlib.Tactic.LibrarySearch

set_option linter.unusedVariables false


attribute [decreasing] Int.neg_pos_of_neg Int.fmod_lt_of_pos 

@[decreasing] theorem lower_bound_fmod (a b : ℤ) (h1 : 0 < b) : -b < Int.fmod a b := by
  have H : 0 ≤ Int.fmod a b 
  · apply Int.fmod_nonneg'
    apply h1
  calc -b < 0 := by addarith [h1]
    _ ≤ _ := H

@[decreasing] theorem upper_bound_fmod (a b : ℤ) (h1 : b < 0) : b < Int.fmod a (-b) := by
  have h2 : 0 < -b := by addarith [h1]
  calc b = - - b := by ring
    _ < Int.fmod a (-b) := lower_bound_fmod a (-b) h2

def gcd (a b : ℤ) : ℤ :=
  if 0 < b then
    gcd b (Int.fmod a b)
  else if b < 0 then
    gcd b (Int.fmod a (-b))
  else if 0 ≤ a then
    a
  else
    -a
termination_by _ a b => b

theorem gcd_nonneg (a b : ℤ) : 0 ≤ gcd a b := by
  rw [gcd]
  split_ifs with h1 h2 ha <;> push_neg at *
  · apply gcd_nonneg
  · apply gcd_nonneg
  · apply ha
  · addarith [ha]
termination_by _ a b => b

#eval gcd 24 15

mutual
theorem gcd_dvd_right (a b : ℤ) : gcd a b ∣ b := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · exact gcd_dvd_left b (Int.fmod a b) --sorry
  · exact gcd_dvd_left b (Int.fmod a (-b))
  · have hb : b = 0 := le_antisymm h1 h2
    take 0
    calc b = 0 := hb
      _ = a * 0 := by ring
  · have hb : b = 0 := le_antisymm h1 h2
    take 0
    calc b = 0 := hb
      _ = -a * 0 := by ring

theorem gcd_dvd_left (a b : ℤ) : gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · have IH1 := gcd_dvd_left b (Int.fmod a b)
    have IH2 := gcd_dvd_right b (Int.fmod a b)
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H : Int.fmod a b + b * Int.fdiv a b = a := Int.fmod_add_fdiv a b
    set q := Int.fdiv a b
    set r := Int.fmod a b
    take k * q + l
    calc a = r + b * q := by rw [H]
      _ = gcd b r * l + (gcd b r * k) * q := by rw [← hk, ← hl] -- EXPLAIN
      _ = gcd b r * (k * q + l) := by ring
  · have IH1 := gcd_dvd_left b (Int.fmod a (-b))
    have IH2 := gcd_dvd_right b (Int.fmod a (-b))
    obtain ⟨k, hk⟩ := IH1
    obtain ⟨l, hl⟩ := IH2
    have H := Int.fmod_add_fdiv a (-b)
    set q := Int.fdiv a (-b)
    set r := Int.fmod a (-b)
    take -k * q + l
    calc a = r + (-b) * q := by rw [H]
      _ = gcd b r * l + (- (gcd b r * k)) * q := by rw [← hk, ← hl] -- EXPLAIN
      _ = gcd b r * (-k * q + l) := by ring
  · take 1
    ring
  · take -1
    ring
end
termination_by gcd_dvd_right a b => b ; gcd_dvd_left a b => b

namespace bezout

mutual

def L (a b : ℤ) : ℤ :=
  if 0 < b then
    R b (Int.fmod a b)
  else if b < 0 then
    R b (Int.fmod a (-b)) 
  else if 0 ≤ a then 
    1
  else
    -1

def R (a b : ℤ) : ℤ :=
  if 0 < b then
    L b (Int.fmod a b) - (Int.fdiv a b) * R b (Int.fmod a b)
  else if b < 0 then
    L b (Int.fmod a (-b)) + (Int.fdiv a (-b)) * R b (Int.fmod a (-b))
  else
    0

end
termination_by L a b => b ; R a b => b

#eval L 24 15
#eval R 24 15

theorem L_mul_add_R_mul (a b : ℤ) : L a b * a + R a b * b = gcd a b := by
  rw [R, L, gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · have := L_mul_add_R_mul b (Int.fmod a b)
    have H : Int.fmod a b + b * Int.fdiv a b = a := Int.fmod_add_fdiv a b
    set q := Int.fdiv a b
    set r := Int.fmod a b
    calc R b r * a + (L b r - q * R b r) * b
        = R b r * (r + b * q) + (L b r - q * R b r) * b:= by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := this
  · have := L_mul_add_R_mul b (Int.fmod a (-b))
    have H : Int.fmod a (-b) + (-b) * Int.fdiv a (-b) = a := Int.fmod_add_fdiv a (-b)
    set q := Int.fdiv a (-b)
    set r := Int.fmod a (-b)
    calc  R b r * a + (L b r + q * R b r) * b 
        =  R b r * (r + -b * q) + (L b r + q * R b r) * b := by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := this
  · ring
  · ring
termination_by L_mul_add_R_mul a b => b

end bezout

open bezout

theorem bezout (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = gcd a b := by
  take L a b, R a b
  apply L_mul_add_R_mul

