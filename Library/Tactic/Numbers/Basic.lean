import Mathlib.Tactic.NormNum

open Lean hiding Rat mkRat
open Lean.Meta Qq Lean.Elab Term
open Lean.Parser.Tactic Mathlib.Meta.NormNum

/--
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` and `^`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions.
-/
elab (name := numbers) "numbers" loc:(location ?) : tactic =>
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)

theorem Prod.ne_left {a1 a2 : A} {b1 b2 : B} : a1 ≠ a2 → (a1, b1) ≠ (a2, b2) := mt <| by
  rw [Prod.mk.inj_iff]
  exact And.left

theorem Prod.ne_right {a1 a2 : A} {b1 b2 : B} : b1 ≠ b2 → (a1, b1) ≠ (a2, b2) := mt <| by
  rw [Prod.mk.inj_iff]
  exact And.right

theorem Prod.ne_left_right {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} (h : b1 ≠ b2) :
    (a1, b1, c1) ≠ (a2, b2, c2) :=
  Prod.ne_right <| Prod.ne_left h

theorem Prod.ne_right_right {a1 a2 : A} {b1 b2 : B} {c1 c2 : C} (h : c1 ≠ c2) :
    (a1, b1, c1) ≠ (a2, b2, c2) :=
  Prod.ne_right <| Prod.ne_right h

macro_rules | `(tactic| numbers) => `(tactic| apply Prod.ext <;> numbers)
macro_rules | `(tactic| numbers) => `(tactic| apply Prod.ne_left ; numbers)
macro_rules | `(tactic| numbers) => `(tactic| apply Prod.ne_right ; numbers)
macro_rules | `(tactic| numbers) => `(tactic| apply Prod.ne_left_right ; numbers)
macro_rules | `(tactic| numbers) => `(tactic| apply Prod.ne_right_right ; numbers)

macro (name := normNumCmd) "#numbers" ppSpace e:term : command =>
  `(command| #conv norm_num1 => $e)

open Tactic

@[inherit_doc numbers] syntax (name := numbersConv) "numbers" : conv

/-- Elaborator for `numbers` conv tactic. -/
@[tactic numbersConv] def elabNormNum1Conv : Tactic := fun _ ↦ withMainContext do
  let ctx ← getSimpContext mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))
