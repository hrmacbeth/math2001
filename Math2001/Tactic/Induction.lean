/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.Cases

/-! # Specialized induction tactics

This file introduces macros for several standard induction principles, in forms optimized for
arithmetic proofs (`Nat.zero` and `Nat.succ` are renamed to `0` and `n + 1`, and `push_cast` is
called pre-emptively on all goals).
-/

@[eliminator] protected def Nat.recAux.{u} {motive : ℕ → Sort u} (base_case : motive 0)
    (inductive_step : (k : ℕ) → (IH : motive k) → motive (k+1)) : (t : ℕ) → motive t
| 0 => base_case
| k+1 => inductive_step k (Nat.recAux base_case inductive_step k)

@[elab_as_elim]
lemma Nat.induction {P : ℕ → Prop} (base_case : P 0)
    (inductive_hypothesis : ∀ k, (IH : P k) → P (k + 1)) : (∀ n, P n) :=
  Nat.rec base_case inductive_hypothesis

@[elab_as_elim]
def Nat.two_step_induction' {P : ℕ → Sort u} (base_case_0 : P 0) (base_case_1 : P 1)
    (inductive_hypothesis : ∀ (k : ℕ), (IH0 : P k) → (IH1 : P (k + 1)) → P (k + 1 + 1)) (a : ℕ) :
    P a :=
  Nat.two_step_induction base_case_0 base_case_1 inductive_hypothesis a

open Lean Parser Category Elab Tactic

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in
syntax (name := BasicInductionSyntax) "simple_induction " (casesTarget,+) (" with " (colGt binderIdent)+)? : tactic

macro_rules
| `(tactic| simple_induction $tgts,* $[with $withArg*]?) =>
    `(tactic| induction' $tgts,* using Nat.induction $[with $withArg*]? <;>
      push_cast (config := { decide := false }))

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in
syntax (name := StartingPointInductionSyntax) "induction_from_starting_point " (casesTarget,+) (" with " (colGt binderIdent)+)? : tactic

macro_rules
| `(tactic| induction_from_starting_point $tgts,* $[with $withArg*]?) =>
    `(tactic| induction' $tgts,* using Nat.le_induction $[with $withArg*]? <;>
      push_cast (config := { decide := false }))

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in
syntax (name := TwoStepInductionSyntax) "two_step_induction " (casesTarget,+) (" with " (colGt binderIdent)+)? : tactic

macro_rules
| `(tactic| two_step_induction $tgts,* $[with $withArg*]?) =>
    `(tactic| induction' $tgts,* using Nat.two_step_induction' $[with $withArg*]? <;>
      push_cast (config := { decide := false }))