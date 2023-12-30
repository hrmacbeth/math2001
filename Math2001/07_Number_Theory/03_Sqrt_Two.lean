/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.GCD
import Library.Theory.NumberTheory

math2001_init


@[decreasing] theorem irrat_aux_wf (b k : ℕ) (hb : k ≠ 0) (hab : b ^ 2 = 2 * k ^ 2) :
    k < b := by
  have h :=
  calc k ^ 2 < k ^ 2 + k ^ 2 := by extra
    _ = 2 * k ^ 2 := by ring
    _ = b ^ 2 := by rw [hab]
  cancel 2 at h



theorem irrat_aux (a b : ℕ) (hb : b ≠ 0) : a ^ 2 ≠ 2 * b ^ 2 := by
  intro hab
  have H : Nat.Even a
  · apply Nat.even_of_pow_even (n := 2)
    use b ^ 2
    apply hab
  obtain ⟨k, hk⟩ := H
  have hbk :=
    calc 2 * b ^ 2 = a ^ 2 := by rw [hab]
      _ = (2 * k) ^ 2 := by rw [hk]
      _ = 2 * (2 * k ^ 2) := by ring
  cancel 2 at hbk
  have hk' :=
    calc 0 < b ^ 2 := by extra
      _ = 2 * k ^ 2 := by rw [hbk]
      _ = k * (2 * k) := by ring
  cancel 2 * k at hk'
  have hk'' : k ≠ 0 := ne_of_gt hk'
  have IH := irrat_aux b k -- inductive hypothesis
  have : b ^ 2 ≠ 2 * k ^ 2 := IH hk''
  contradiction
termination_by _ => b


example : ¬ ∃ a b : ℕ, b ≠ 0 ∧ a ^ 2 = 2 * b ^ 2 := by
  intro h
  obtain ⟨a, b, hb, hab⟩ := h
  have := irrat_aux a b hb
  contradiction


example : ¬ ∃ a b : ℤ, b ≠ 0 ∧ b ^ 2 = 2 * a ^ 2 := by
  intro h
  obtain ⟨a, b, hb, hab⟩ := h
  have Ha : gcd a b ∣ a := gcd_dvd_left a b
  have Hb : gcd a b ∣ b := gcd_dvd_right a b
  obtain ⟨k, hk⟩ := Ha
  obtain ⟨l, hl⟩ := Hb
  obtain ⟨x, y, h⟩ := bezout a b
  set d := gcd a b
  have key :=
  calc (2 * k * y + l * x) ^ 2 * d ^ 2
      = (2 * (d * k) * y + (d * l) * x) ^ 2 := by ring
    _ = (2 * a * y + b * x) ^ 2 := by rw [hk, hl]
    _ = 2 * (x * a + y * b) ^ 2 + (x ^ 2 - 2 * y ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
    _ = 2 * d ^ 2 + (x ^ 2 - 2 * y ^ 2) * (b ^ 2 - b ^ 2) := by rw [h, hab]
    _ = 2 * d ^ 2 := by ring
  have hd : d ≠ 0
  · intro hd
    have :=
    calc b = d * l := hl
      _ = 0 * l := by rw [hd]
      _ = 0 := by ring
    contradiction
  cancel d ^ 2 at key
  have := sq_ne_two (2 * k * y + l * x)
  contradiction
