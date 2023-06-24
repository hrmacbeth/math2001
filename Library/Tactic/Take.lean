/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner, Moritz Doll
-/

import Mathlib.Tactic.Basic

namespace Mathlib.Tactic

/--
`take e₁, e₂, ⋯` is used to advance on existential goals, for which terms as
well as proofs of some claims about them are expected.

Examples:

```lean
example : ∃ x : Nat, x = x := by
  take 42
  ring

example : ∃ x : Nat, ∃ y : Nat, x = y := by
  take 42, 42
  ring

example : ∃ x : String × String, x.1 = x.2 := by
  take ("forty-two", "forty-two")
  rfl
```
-/
macro "take " es:term,+ : tactic =>
  `(tactic|refine ⟨$es,*, ?_⟩)
