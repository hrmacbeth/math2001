/- Copyright (c) 2023 Heather Macbeth. All rights reserved. -/
import Mathlib.Tactic.Ring

/-! In this file we let `ring` silently operate as `ring_nf` (the recursive normalization form of
`ring`) when (1) it is used in conv mode, or (2) it is used terminally.  We also make it fail for
nonterminal use. -/

macro_rules | `(conv | ring) => `(conv | ring_nf)
macro "ring" : tactic => `(tactic | first | (ring_nf; done) | ring1)
