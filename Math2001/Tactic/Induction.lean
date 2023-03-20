/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Have

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
theorem Nat.induction {P : ℕ → Prop} (base_case : P 0)
    (inductive_step : ∀ k, (IH : P k) → P (k + 1)) : (∀ n, P n) :=
  Nat.rec base_case inductive_step

@[elab_as_elim]
def Nat.two_step_induction' {P : ℕ → Sort u} (base_case_0 : P 0) (base_case_1 : P 1)
    (inductive_step : ∀ (k : ℕ), (IH0 : P k) → (IH1 : P (k + 1)) → P (k + 1 + 1)) (a : ℕ) :
    P a :=
  Nat.two_step_induction base_case_0 base_case_1 inductive_step a

@[elab_as_elim]
theorem Int.induction_on' {p : ℤ → Prop} (base_case : p 0)
    (forward_inductive_step : ∀ (i : ℤ) (hi : 0 ≤ i) (IH : p i),  p (i + 1))
    (backward_inductive_step : ∀ (i : ℤ) (hi : i ≤ 0) (IH : p i), p (i - 1)) (i : ℤ) :
    p i := by
  refine Int.induction_on i base_case (fun i hi ↦ ?_) (fun i hi ↦ ?_)
  · exact forward_inductive_step _ (Int.ofNat_nonneg i) hi
  · exact backward_inductive_step _ (Int.neg_le_of_neg_le (Int.ofNat_nonneg i)) hi

@[elab_as_elim]
theorem Nat.strong_induction_succ {p : (n : ℕ) → Sort _} (base_case : p 0) 
    (inductive_step : ∀ (k : ℕ), (∀ (m : ℕ), m ≤ k → p m) → p (k + 1)) :
    ∀ n : ℕ, p n
  | 0 => base_case
  | k + 1 => by
      induction' k using Nat.strong_rec_on with l IH
      apply inductive_step
      intro m hm
      match m with
      | 0 => apply base_case
      | t + 1 => apply IH _ hm

@[elab_as_elim]
theorem Nat.strong_le_induction {s : ℕ} {p : (n : ℕ) → s ≤ n → Prop} 
    (inductive_step : ∀ (k : ℕ) (hk : s ≤ k), (∀ (m : ℕ) (hm : s ≤ m), m < k → p m hm) → p k hk)
    (n : ℕ) (hn : s ≤ n) : p n hn := by
  let P : ℕ → Prop := fun (n : ℕ) ↦ ∀ (k : ℕ) (hk : s ≤ k), k ≤ n → p k hk
  have h : ∀ (m : ℕ), s ≤ m → P m
  · refine Nat.le_induction ?_ ?_
    · show ∀ (k : ℕ) (hk : s ≤ k), k ≤ s → p k hk
      intro k hk hk'
      apply inductive_step
      intro m hm hm'
      have := not_lt_of_le <| hk'.trans hm
      contradiction
    intro k _ IH m hm hm'
    apply inductive_step
    intro l hl hl'
    apply IH
    apply le_of_lt_succ
    exact lt_of_lt_of_le hl' hm'
  apply h n hn
  apply le_refl

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

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in
syntax (name := IntInductionSyntax) "integer_induction " (casesTarget,+) (" with " (colGt binderIdent)+)? : tactic

macro_rules
| `(tactic| integer_induction $tgts,* $[with $withArg*]?) =>
    `(tactic| induction' $tgts,* using Int.induction_on' $[with $withArg*]? <;>
      push_cast (config := { decide := false }))

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in
syntax (name := StrongInductionSyntax) "strong_induction " (casesTarget,+) (" with " (colGt binderIdent)+)? : tactic

macro_rules
| `(tactic| strong_induction $tgts,* $[with $withArg*]?) =>
    `(tactic| induction' $tgts,* using Nat.strong_induction_on $[with $withArg*]? <;>
      push_cast (config := { decide := false }))

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in
syntax (name := StrongInductionOneSyntax) "strong_induction_from_one " (casesTarget,+) (" with " (colGt binderIdent)+)? : tactic

macro_rules
| `(tactic| strong_induction_from_one $tgts,* $[with $withArg*]?) =>
    `(tactic| induction' $tgts,* using Nat.strong_induction_succ $[with $withArg*]? <;>
      push_cast (config := { decide := false }))

open private getElimNameInfo generalizeTargets generalizeVars in evalInduction in
syntax (name := StartingPointStrongInductionSyntax) "strong_induction_from_starting_point " (casesTarget,+) (" with " (colGt binderIdent)+)? : tactic

macro_rules
| `(tactic| strong_induction_from_starting_point $tgts,* $[with $withArg*]?) =>
    `(tactic| induction' $tgts,* using Nat.strong_le_induction $[with $withArg*]? <;>
      push_cast (config := { decide := false }))