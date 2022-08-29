/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import algebra.order.ring
import tactic

lemma eq_zero_of_mul_pos_eq_zero {α : Type*} [linear_ordered_semiring α] {b : α} (a : α)
  (h : a * b = 0) (ha : 0 < a) :
  b = 0 :=
begin
  apply le_antisymm,
  apply nonpos_of_mul_nonpos_right,
  calc a * b = 0 : by rw h
  ... ≤ 0 : by norm_num,
  apply ha,
  apply nonneg_of_mul_nonneg_right,
  calc 0 ≤ 0 : by norm_num
  ... = a * b : by rw h,
  apply ha,
end

lemma eq_zero_of_mul_neg_eq_zero {α : Type*} [linear_ordered_ring α] {b : α} (a : α)
  (h : a * b = 0) (ha : a < 0) :
  b = 0 :=
begin
  apply le_antisymm,
  apply nonpos_of_mul_nonneg_right,
  calc 0 ≤ 0 : by norm_num
  ... = a * b : by rw h,
  apply ha,
  apply nonneg_of_mul_nonpos_right,
  calc a * b = 0 : by rw h
  ... ≤ 0 : by norm_num,
  apply ha,
end