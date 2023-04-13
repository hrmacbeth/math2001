/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Prod.Basic

macro_rules | `(tactic| constructor) => `(tactic| rw [Prod.mk.inj_iff] ; apply And.intro)

-- example (h : x = 1) : (x, 3) = (1, 3) := by
--   constructor

open Std.Tactic.RCases Lean.Parser in
macro_rules
| `(tactic| obtain $pat := $val) =>
    `(tactic| 
      rw [Prod.mk.inj_iff] at * ; 
      obtain $pat := $val)

-- example (h : (x, 3) = (1, 3)) : sorry := by
--   -- rw [Prod.mk.inj_iff] at *
--   obtain ⟨h1, h2⟩ := h

  