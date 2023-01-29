/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.SolveByElim

register_tag_attr ineq_rules

register_tag_attr ineq_extra

register_tag_attr mod_rules

register_tag_attr mod_extra

syntax (name := RelSyntax) "rel" " [" term,* "] " : tactic
syntax (name := ExtraSyntax) "extra" : tactic

open Lean Mathlib Tactic

def RelConfig : SolveByElim.Config :=
{ transparency := .instances
  -- On applying a lemma or hypothesis successfully, don't backtrack
  discharge := fun _ => pure none
  failAtMaxDepth := false
  maxDepth := 50 }

def Lean.MVarId.Rel (disch : MVarId → MetaM (Option (List MVarId))) (attr : Name)
    (add : List Term) (m : MessageData) (g : MVarId) :
    MetaM (List MVarId) := do
  let cfg : SolveByElim.Config := { RelConfig with discharge := disch }
  let [] ← SolveByElim.solveByElim.processSyntax cfg true false add [] #[mkIdent attr] [g]
    | throwError m
  return []
