/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Lemmas

theorem eq_zero_of_mul_neg_eq_zero [LinearOrderedRing α]
    {b : α} (a : α) (H1 : a * b = 0) (H2 : a < 0) :
    b = 0 :=
  le_antisymm (nonpos_of_mul_nonneg_right H1.ge H2) (nonneg_of_mul_nonpos_right H1.le H2)

theorem eq_zero_of_mul_pos_eq_zero [LinearOrderedRing α]
    {b : α} (a : α) (H1 : a * b = 0) (H2 : 0 < a) :
    b = 0 :=
  le_antisymm (nonpos_of_mul_nonpos_right H1.le H2) (nonneg_of_mul_nonneg_right H1.ge H2)
