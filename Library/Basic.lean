import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Library.Config.Constructor
import Library.Config.Contradiction
import Library.Config.ExistsDelaborator
import Library.Config.Initialize
import Library.Config.Ring
import Library.Config.Set
import Library.Config.Use
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Extra.Basic
import Library.Tactic.Induction
import Library.Tactic.Numbers.Basic
import Library.Tactic.Obtain
import Library.Tactic.TruthTable

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

macro "linarith" linarithArgsRest : tactic => `(tactic | fail "linarith tactic disabled")
macro "nlinarith" linarithArgsRest : tactic => `(tactic | fail "nlinarith tactic disabled")
macro "linarith!" linarithArgsRest : tactic => `(tactic | fail "linarith! tactic disabled")
macro "nlinarith!" linarithArgsRest : tactic => `(tactic | fail "nlinarith! tactic disabled")
macro "polyrith" : tactic => `(tactic | fail "polyrith tactic disabled")
macro "decide" : tactic => `(tactic | fail "decide tactic disabled")
macro "aesop" : tactic => `(tactic | fail "aesop tactic disabled")
macro "tauto" : tactic => `(tactic | fail "tauto tactic disabled")

open Lean.Parser.Tactic in
macro "simp"  (&" only")?  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")?
  (location)? : tactic => `(tactic | fail "simp tactic disabled")

/--
Configure the environment with the right options and attributes
for the book *The Mechanics of Proof*.

Tries to perform essentially the following:

```
set_option push_neg.use_distrib true

attribute [-simp] ne_eq
attribute [-ext] Prod.ext
attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat
attribute [-norm_num] Mathlib.Meta.NormNum.evalNatDvd
  Mathlib.Meta.NormNum.evalIntDvd
```
-/
elab "math2001_init" : command => do
  trySetOptions #[
    ⟨`push_neg.use_distrib, true⟩
  ]
  tryEraseAttrs #[
    ⟨`simp, #[`ne_eq]⟩,
    ⟨`ext, #[`Prod.ext]⟩,
    ⟨`instance, #[`Int.instDivInt_1,`Int.instDivInt, `Nat.instDivNat]⟩,
    ⟨`norm_num, #[`Mathlib.Meta.NormNum.evalNatDvd, `Mathlib.Meta.NormNum.evalIntDvd]⟩
  ]
