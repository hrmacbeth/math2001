/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import Library.Theory.GCD

math2001_init


theorem gauss_lemma {d a b : ℤ} (h1 : d ∣ a * b) (h2 : gcd a d = 1) : d ∣ b := by
  obtain ⟨x, y, h⟩ := bezout a d
  obtain ⟨z, hz⟩ := h1
  use x * z + b * y
  calc b = b * 1 := by ring
    _ = b * gcd a d := by rw [h2]
    _ = b * (x * a + y * d) := by rw [h]
    _ = x * (a * b) + b * y * d := by ring
    _ = x * (d * z) + b * y * d := by rw [hz]
    _ = d * (x * z + b * y) := by ring


theorem euclid_lemma {a b p : ℕ} (hp : Prime p) (H : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  -- write down everything we know about `gcd (a:ℤ) (p:ℤ)`
  have hap1 : gcd (a:ℤ) (p:ℤ) ∣ (a:ℤ) := gcd_dvd_left (a:ℤ) (p:ℤ)
  have hap2 : gcd (a:ℤ) (p:ℤ) ∣ (p:ℤ) := gcd_dvd_right (a:ℤ) (p:ℤ)
  have h_gauss : (p:ℤ) ∣ (a:ℤ) * (b:ℤ) → gcd (a:ℤ) (p:ℤ) = 1 → (p:ℤ) ∣ (b:ℤ) :=
    gauss_lemma
  have hgcd : 0 ≤ gcd (a:ℤ) (p:ℤ) := gcd_nonneg (a:ℤ) (p:ℤ)
  -- convert to `ℕ` facts
  lift gcd a p to ℕ using hgcd with d hd
  norm_cast at hap1 hap2 h_gauss
  -- actually prove the theorem
  dsimp [Prime] at hp
  obtain ⟨hp1, hp2⟩ := hp
  obtain hgcd_1 | hgcd_p : d = 1 ∨ d = p := hp2 d hap2
  · right
    apply h_gauss H hgcd_1
  · left
    rw [← hgcd_p]
    apply hap1


theorem euclid_lemma_pow (a k p : ℕ) (hp : Prime p) (hk : 1 ≤ k) (H : p ∣ a ^ k) :
    p ∣ a := by
  induction_from_starting_point k, hk with t ht IH
  · have ha : a ^ 1 = a := by ring
    rw [ha] at H
    apply H
  have ha : a ^ (t + 1) = a * a ^ t := by ring
  rw [ha] at H
  have key : p ∣ a ∨ p ∣ a ^ t := euclid_lemma hp H
  obtain h1 | h2 := key
  · apply h1
  · apply IH
    apply h2
