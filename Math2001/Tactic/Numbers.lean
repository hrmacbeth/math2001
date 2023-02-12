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

macro (name := normNumCmd) "#numbers" ppSpace e:term : command =>
  `(command| #conv norm_num1 => $e)
