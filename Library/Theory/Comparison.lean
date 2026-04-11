/- Copyright (c) Mario Carneiro, 2023. -/
import Mathlib.Order.Basic

macro "le_or_succ_le" a:term:arg n:num  : term =>
  `(show $a ≤ $n ∨ $(Lean.quote (n.getNat+1)) ≤ $a from le_or_gt ..)

