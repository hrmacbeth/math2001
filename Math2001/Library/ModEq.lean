/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Math2001.Library.Division

/-- Two integers are congruent modulo `n`, if their difference is a multiple of `n`. -/
def Int.ModEq (n a b : ℤ) : Prop := n ∣ a - b

notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

protected theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := ⟨0, by ring⟩

protected theorem Int.ModEq.add (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  exact ⟨x + y, by linear_combination hx + hy⟩ 

protected theorem Int.ModEq.add_left (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
(Int.ModEq.refl _).add h

protected theorem Int.ModEq.add_right (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
h.add (Int.ModEq.refl _)

protected theorem Int.ModEq.sub (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  exact ⟨x - y, by linear_combination hx - hy⟩ 

protected theorem Int.ModEq.sub_left (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
(Int.ModEq.refl _).sub h

protected theorem Int.ModEq.sub_right (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
h.sub (Int.ModEq.refl _)

protected theorem Int.ModEq.neg (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  exact ⟨-x, by linear_combination -hx⟩ 

protected theorem Int.ModEq.mul (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  exact ⟨x * c + b * y, by linear_combination c * hx + b * hy⟩

protected theorem Int.ModEq.mul_left (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
(Int.ModEq.refl _).mul h

protected theorem Int.ModEq.mul_right (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
h.mul (Int.ModEq.refl _)

protected theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] := by
  induction k
  case zero => exact Int.ModEq.refl _
  case succ k hk => exact Int.ModEq.mul hk h

protected theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  exact ⟨-x, by linear_combination - hx⟩

@[trans]
protected theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) : a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  exact ⟨x + y, by linear_combination hx + hy⟩

instance : IsTrans ℤ (Int.ModEq n) where
  trans := @Int.ModEq.trans n

theorem Int.modEq_fac_zero : n * t ≡ 0 [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_fac_zero' : t * n ≡ 0 [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_zero_fac : 0 ≡ n * t [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_zero_fac' : 0 ≡ t * n [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_add_fac_self : a + n * t ≡ a [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_add_fac_self' : n * t + a ≡ a [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_add_fac_self'' : a + t * n ≡ a [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_add_fac_self''' : t * n + a ≡ a [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_sub_fac_self : a - n * t ≡ a [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_sub_fac_self' : n * t - a ≡ -a [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_sub_fac_self'' : a - t * n ≡ a [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_sub_fac_self''' : t * n - a ≡ -a [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_add_fac_self_symm : a ≡ a + n * t [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_add_fac_self_symm' : a ≡ n * t + a [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_add_fac_self_symm'' : a ≡ a + t * n [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_add_fac_self_symm''' : a ≡ t * n + a [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_sub_fac_self_symm : a ≡ a - n * t [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_sub_fac_self_symm' : -a ≡ n * t - a [ZMOD n] := ⟨-t, by ring⟩
theorem Int.modEq_sub_fac_self_symm'' : a ≡ a - t * n [ZMOD n] := ⟨t, by ring⟩
theorem Int.modEq_sub_fac_self_symm''' : -a ≡ t * n - a [ZMOD n] := ⟨-t, by ring⟩

theorem Int.existsUnique_modEq_lt (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  obtain ⟨r, ⟨rpos, rlt, q, hq⟩, hr2⟩ := a.existsUnique_quotient_remainder b hb
  refine ⟨r, ⟨rpos, rlt, q, ?_⟩, ?_⟩ <;> dsimp at *
  . linear_combination hq
  rintro r' ⟨rpos', rlt', q', hq'⟩ 
  refine hr2 r' ⟨rpos', rlt', q', ?_⟩ 
  linear_combination hq'