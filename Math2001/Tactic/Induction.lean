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

@[elab_as_elim]
lemma Nat.induction {P : ℕ → Prop} : P 0 → (∀ n, P n → P (n + 1)) → (∀ n, P n) :=
  Nat.rec

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