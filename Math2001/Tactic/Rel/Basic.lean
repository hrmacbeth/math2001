/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SolveByElim
import Math2001.Tactic.Rel.Attr
import Mathlib.Tactic.LibrarySearch

open Lean Meta Elab
open Mathlib Tactic

def RelConfig : SolveByElim.Config :=
{ transparency := .instances
  -- On applying a lemma or hypothesis successfully, don't backtrack
  discharge := fun _ => pure none
  failAtMaxDepth := false
  maxDepth := 50 }

/-- On applying a lemma or hypothesis successfully, attempt to resolve remaining goals with
`positivity`, but even if that fails, don't backtrack -/
def IneqRelDischarge (g : MVarId) : MetaM (Option (List MVarId)) :=
do withTransparency .reducible (Meta.Positivity.positivity g); pure (some []) <|> pure none

def Lean.MVarId.Rel (disch : MVarId → MetaM (Option (List MVarId))) (attr : Name)
    (add : List Term) (m : MessageData) (g : MVarId) :
    MetaM (List MVarId) := do
  let cfg : SolveByElim.Config := { RelConfig with discharge := disch }
  let [] ← SolveByElim.solveByElim.processSyntax cfg true false add [] #[mkIdent attr] [g]
    | throwError m
  return []

syntax (name := IneqRelSyntax) "ineq_rel" " [" term,* "] " : tactic
syntax (name := ModRelSyntax) "mod_rel" " [" term,* "] " : tactic
syntax (name := RelSyntax) "rel" " [" term,* "] " : tactic

elab_rules : tactic | `(tactic| ineq_rel [$t,*]) => do
  liftMetaTactic <|
    Lean.MVarId.Rel IneqRelDischarge `ineq_rules t.getElems.toList
      "cannot prove this by 'substituting' the listed relationships"

elab_rules : tactic | `(tactic| mod_rel [$t,*]) => do
  liftMetaTactic <|
    Lean.MVarId.Rel (fun _ => pure none) `mod_rules t.getElems.toList
      "cannot prove this by 'substituting' the listed relationships"

macro_rules | `(tactic| rel [$t,*]) => `(tactic| ineq_rel [$t,*])
macro_rules | `(tactic| rel [$t,*]) => `(tactic| mod_rel [$t,*])

syntax (name := IneqExtraSyntax) "ineq_extra" : tactic
syntax (name := ModExtraSyntax) "mod_extra" : tactic
syntax (name := ExtraSyntax) "extra" : tactic

elab_rules : tactic | `(tactic| ineq_extra) => do
  liftMetaTactic <|
    Lean.MVarId.Rel IneqRelDischarge `ineq_extra []
      "the two sides don't differ by a neutral quantity for the relation"

elab_rules : tactic | `(tactic| mod_extra) => do
  liftMetaTactic <|
    Lean.MVarId.Rel (fun _ => pure none) `mod_extra []
      "the two sides don't differ by a neutral quantity for the relation"

macro_rules | `(tactic| extra) => `(tactic| ineq_extra)
macro_rules | `(tactic| extra) => `(tactic| mod_extra)

attribute [ineq_rules]
  le_refl
  -- deliberately no `add_lt_add` since this is an unsafe lemma appplication in the context
  add_le_add add_lt_add_left add_lt_add_right
  sub_le_sub sub_lt_sub_left sub_lt_sub_right
  mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right
  mul_le_mul_of_nonpos_left mul_le_mul_of_nonpos_right
  mul_lt_mul_of_pos_left mul_lt_mul_of_pos_right
  div_le_div_of_le div_lt_div_of_lt
  pow_le_pow_of_le_left pow_lt_pow_of_lt_left
  -- want to apply this only forward on hypotheses, not backward on a general goal
  -- put it last but would be good to implement directly as forward reasoning
  le_of_lt

lemma IneqExtra.neg_le_sub_self_of_nonneg [LinearOrderedAddCommGroup G] {a b : G} (h : 0 ≤ a) :
    -b ≤ a - b := by
  rw [sub_eq_add_neg]
  apply le_add_of_nonneg_left h

attribute [ineq_extra]
  le_add_of_nonneg_right le_add_of_nonneg_left
  lt_add_of_pos_right lt_add_of_pos_left
  IneqExtra.neg_le_sub_self_of_nonneg
  add_le_add_left add_le_add_right add_lt_add_left add_lt_add_right
  sub_le_sub_left sub_le_sub_right sub_lt_sub_left sub_lt_sub_right

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

attribute [mod_extra]
  Int.modEq_add_fac_self Int.modEq_add_fac_self' Int.modEq_add_fac_self'' Int.modEq_add_fac_self'''
  Int.modEq_sub_fac_self Int.modEq_sub_fac_self' Int.modEq_sub_fac_self'' Int.modEq_sub_fac_self'''
  Int.ModEq.add_right Int.ModEq.add_left
  Int.ModEq.sub_right Int.ModEq.sub_left

