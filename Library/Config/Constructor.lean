/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Prod.Basic

/-! In mainstream Lean, goals with the logical structure `∧` or `↔` are decomposed into their
constituent parts using the `constructor` tactic.  This is a powerful tactic and it will attempt
to do something reasonable on other inductive-predicate types too, like `∨` (where it behaves the
same as `left`) and `∃` (where it will introduce a metavariable for the witness) .... all of which
is very confusing for novice users.
This file redefines the tactic `constructor` to work only on `∧` and `↔` goals.

(In fact this is a slight simplification: in the mental model of this book, an
equality in a product type is by definition a conjunction of co-ordinate-wise equalities, so we also
allow `constructor` to make progress on such goals.)  -/

theorem Prod.congr {a1 a2 : A} {b1 b2 : B} (h : a1 = a2 ∧ b1 = b2) : (a1, b1) = (a2, b2) :=
  Iff.mpr Prod.mk.inj_iff h

/-- The `constructor` tactic operates on goals of the form `P ∧ Q` or `P ↔ Q`, reducing to the two
constituent subgoals: `P` and `Q` for `∧`, `P → Q` and `Q → P` for `↔`. -/
macro "constructor" : tactic =>
  `(tactic| first
      | refine And.intro ?_ ?_
      | refine Iff.intro ?_ ?_
      | refine Prod.congr (And.intro ?_ ?_)
      | fail "constructor only applies to ∧ and ↔ goals")
