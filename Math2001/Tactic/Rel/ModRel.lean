/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Int.ModEq
import Math2001.Tactic.Rel.Basic

open Lean Elab Tactic

syntax (name := ModRelSyntax) "mod_rel" " [" term,* "] " : tactic

elab_rules : tactic | `(tactic| mod_rel [$t,*]) => do
  liftMetaTactic <|
    Lean.MVarId.Rel (fun _ => pure none) `mod_rules t.getElems.toList
      "cannot prove this by 'substituting' the listed relationships"

macro_rules | `(tactic| rel [$t,*]) => `(tactic| mod_rel [$t,*])

syntax (name := ModExtraSyntax) "mod_extra" : tactic

elab_rules : tactic | `(tactic| mod_extra) => do
  liftMetaTactic <|
    Lean.MVarId.Rel (fun _ => pure none) `mod_extra []
      "the two sides don't differ by a neutral quantity for the relation"

macro_rules | `(tactic| extra) => `(tactic| mod_extra)

attribute [mod_rules]
  Int.ModEq.refl
  -- hopefully, the order here prioritizes `add_right` and `add_left` over `add`
  Int.ModEq.add_right Int.ModEq.add_left Int.ModEq.add
  Int.ModEq.sub_right Int.ModEq.sub_left Int.ModEq.sub
  Int.ModEq.mul_right Int.ModEq.mul_left Int.ModEq.mul
  Int.ModEq.neg Int.ModEq.pow

theorem Int.modEq_add_fac_self' : n * t + a ≡ a [ZMOD n] := by
  rw [add_comm]
  apply Int.modEq_add_fac_self

theorem Int.modEq_add_fac_self'' : a + t * n ≡ a [ZMOD n] := by
  rw [mul_comm]
  apply Int.modEq_add_fac_self

theorem Int.modEq_add_fac_self''' : t * n + a ≡ a [ZMOD n] := by
  rw [add_comm]
  apply Int.modEq_add_fac_self''

theorem Int.modEq_sub_fac_self : a - n * t ≡ a [ZMOD n] := by
  rw [sub_eq_add_neg, ← mul_neg]
  apply Int.modEq_add_fac_self

theorem Int.modEq_sub_fac_self' : n * t - a ≡ -a [ZMOD n] := by
  rw [sub_eq_add_neg]
  apply Int.modEq_add_fac_self'

theorem Int.modEq_sub_fac_self'' : a - t * n ≡ a [ZMOD n] := by
  rw [mul_comm]
  apply Int.modEq_sub_fac_self

theorem Int.modEq_sub_fac_self''' : t * n - a ≡ -a [ZMOD n] := by
  rw [sub_eq_add_neg]
  apply Int.modEq_add_fac_self'''

theorem Int.modEq_add_fac_self_symm : a ≡ a + n * t [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_add_fac_self

theorem Int.modEq_add_fac_self_symm' : a ≡ n * t + a [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_add_fac_self'

theorem Int.modEq_add_fac_self_symm'' : a ≡ a + t * n [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_add_fac_self''

theorem Int.modEq_add_fac_self_symm''' : a ≡ t * n + a [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_add_fac_self'''

theorem Int.modEq_sub_fac_self_symm : a ≡ a - n * t [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_sub_fac_self

theorem Int.modEq_sub_fac_self_symm' : -a ≡ n * t - a [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_sub_fac_self'

theorem Int.modEq_sub_fac_self_symm'' : a ≡ a - t * n [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_sub_fac_self''

theorem Int.modEq_sub_fac_self_symm''' : -a ≡ t * n - a [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_add_fac_self'''

attribute [mod_extra]
  Int.modEq_add_fac_self Int.modEq_add_fac_self' Int.modEq_add_fac_self'' Int.modEq_add_fac_self'''
  Int.modEq_sub_fac_self Int.modEq_sub_fac_self' Int.modEq_sub_fac_self'' Int.modEq_sub_fac_self'''
  Int.modEq_add_fac_self_symm Int.modEq_add_fac_self_symm' Int.modEq_add_fac_self_symm'' Int.modEq_add_fac_self_symm'''
  Int.modEq_sub_fac_self_symm Int.modEq_sub_fac_self_symm' Int.modEq_sub_fac_self_symm'' Int.modEq_sub_fac_self_symm'''
  Int.ModEq.add_right Int.ModEq.add_left
  Int.ModEq.sub_right Int.ModEq.sub_left

