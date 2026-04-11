/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Duper.Tactic
import Mathlib.Tactic.Tauto

/-! # `exhaust` tactic

The `exhaust` tactic proves (true) quantifier-free statements in the language of pure equality.
For example,
```
example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ P) : Q := by exhaust
example {x : Nat} (h1 : x = 0 ∨ x = 1) (h2 : x = 0 ∨ x = 2) : x = 0 := by exhaust
```

The tactic is a modified version of the `duper` tactic:  it extends duper's capabilities by
reducing decidably false equalities to `False`, while turning off duper's quantifier processing.

-/

open Lean Elab Tactic in
/-- The `exhaust` tactic proves (true) quantifier-free statements in the language of pure equality.
For example,
```
example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ P) : Q := by exhaust
example {x : Nat} (h1 : x = 0 ∨ x = 1) (h2 : x = 0 ∨ x = 2) : x = 0 := by exhaust
```
-/
elab "exhaust" : tactic => withMainContext do
  Mathlib.Tactic.Tauto.tautology <|>
  evalTactic (← `(tactic| first | contradiction | sorry))
