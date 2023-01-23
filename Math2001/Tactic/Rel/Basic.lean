/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SolveByElim
import Math2001.Tactic.Rel.Attr

open Lean Meta Elab Tactic Syntax
open Mathlib Tactic SolveByElim

def RelConfig : SolveByElim.Config :=
{ transparency := .reducible
  -- On applying a lemma or hypothesis successfully, don't backtrack
  discharge := fun _ => pure none
  failAtMaxDepth := false
  maxDepth := 50 }

/-- On applying a lemma or hypothesis successfully, attempt to resolve remaining goals with
`positivity`, but even if that fails, don't backtrack -/
def IneqRelDischarge (g : MVarId) : MetaM (Option (List MVarId)) :=
do withTransparency .reducible (Meta.Positivity.positivity g); pure (some []) <|> pure none

syntax (name := ineqRelSyntax) "rel" (args)? : tactic

def Lean.MVarId.Rel (disch : MVarId → MetaM (Option (List MVarId))) (attr : Name)
    (add : List Term) (g : MVarId) :
    MetaM (List MVarId) := do
  let cfg : SolveByElim.Config := { RelConfig with discharge := disch }
  solveByElim.processSyntax cfg true false add [] #[mkIdent attr] [g]

elab_rules : tactic | `(tactic| rel $[$t:args]?) => do
  let (_, add, _) := parseArgs t
  liftMetaTactic <| Lean.MVarId.Rel IneqRelDischarge `ineq_rules add

syntax (name := modRwSyntax) "mod_rel" (args)? : tactic

elab_rules : tactic | `(tactic| mod_rel $[$t:args]?) => do
  let (_, add, _) := parseArgs t
  liftMetaTactic <| Lean.MVarId.Rel (fun _ => pure none) `mod_rules add

attribute [ineq_rules]
  le_refl
  -- might move these first ones to a different tactic `extra`
  le_add_of_nonneg_right le_add_of_nonneg_left
  lt_add_of_pos_right lt_add_of_pos_left
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

attribute [mod_rules]
  Int.ModEq.refl
  -- hopefully, the order here prioritizes `add_right` and `add_left` over `add`
  Int.ModEq.add_right Int.ModEq.add_left Int.ModEq.add
  Int.ModEq.sub_right Int.ModEq.sub_left Int.ModEq.sub
  Int.ModEq.mul_right Int.ModEq.mul_left Int.ModEq.mul
  Int.ModEq.neg Int.ModEq.pow

