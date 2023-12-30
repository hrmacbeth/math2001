/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.SolveByElim

/-! # `numbers` tactic

The `numbers` tactic is a light modification of the Mathlib `norm_num1` tactic, to
(1) be finishing-only (it does not carry out normalizations mid-proof); the motivation for this is
    that such "normalization" proof steps are awkward to translate to prose proofs, so learning to
    work around them leads to better writing style;
(2) handle equalities and disequalities in product types;
(3) have a cleaner name (the `norm_num1` tactic is a variant of the more cleanly named `norm_num`,
    but that tactic, which incorporates `simp` calls, can confuse students by solving goals which
    seem to have nothing to do with the core "numbers" remit).

It is often convenient for teaching to further modify `norm_num1`/`numbers` by disabling some of the
`norm_num` extensions, when they perform calculations you wish your students to carry out by hand.
This can be done via an initializion command which is run in each file; for example, the
`math2001_init` command in this repository disables the `norm_num` extensions
`Mathlib.Meta.NormNum.evalNatDvd` and `Mathlib.Meta.NormNum.evalIntDvd`. -/

open Lean Meta Elab
open Parser.Tactic Mathlib.Meta.NormNum

def Library.Tactic.numbersDischarger (g : MVarId): MetaM (Option (List MVarId)) :=
  Term.TermElabM.run' do
  match ← Tactic.run g <|
    elabNormNum mkNullNode Syntax.missing (simpOnly := true) (useSimp := false) with
  | [] => pure (some [])
  | _ => failure

theorem Prod.ne_left {a1 a2 : A} {b1 b2 : B} : a1 ≠ a2 → (a1, b1) ≠ (a2, b2) := mt <| by
  rw [Prod.mk.inj_iff]
  exact And.left

theorem Prod.ne_right {a1 a2 : A} {b1 b2 : B} : b1 ≠ b2 → (a1, b1) ≠ (a2, b2) := mt <| by
  rw [Prod.mk.inj_iff]
  exact And.right

theorem Prod.ext' {a1 a2 : A} {b1 b2 : B} (h1 : a1 = a2) (h2 : b1 = b2) : (a1, b1) = (a2, b2) :=
  Prod.ext h1 h2

def Library.Tactic.numbersProdLemmas : List Name := [``Prod.ne_left, ``Prod.ne_right, ``Prod.ext']

/--
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` and `^`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions.
-/
elab (name := numbers) "numbers" : tactic =>
  Tactic.liftMetaTactic <| fun g => do
    let cfg : Mathlib.Tactic.SolveByElim.Config :=
      { maxDepth := 8, discharge := Library.Tactic.numbersDischarger, exfalso := false,
        symm := false  }
    let lemmas := Library.Tactic.numbersProdLemmas.map (liftM <| mkConstWithFreshMVarLevels ·)
    Mathlib.Tactic.SolveByElim.solveByElim cfg lemmas (ctx := pure []) [g]
      <|> throwError "Numbers tactic failed. Maybe the goal is not in scope for the tactic (i.e. the goal is not a pure numeric statement), or maybe the goal is false?"

elab (name := numbersCore) "numbers_core" loc:(location ?) : tactic => do
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)
  Tactic.done

@[inherit_doc numbers]
macro (name := numbersAt) "numbers" loc:location : tactic => `(tactic | numbers_core $loc)

macro (name := normNumCmd) "#numbers" ppSpace e:term : command =>
  `(command| #conv norm_num1 => $e)

open Tactic

@[inherit_doc numbers] syntax (name := numbersConv) "numbers" : conv

/-- Elaborator for `numbers` conv tactic. -/
@[tactic numbersConv] def elabNormNum1Conv : Tactic := fun _ ↦ withMainContext do
  let ctx ← getSimpContext mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))
