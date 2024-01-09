/- Copyright (c) 2024 Heather Macbeth. All rights reserved. -/
import Lean

/-! In this file we turn off the default bundling of `decide` with the `contradiction` tactic. -/

open Lean Meta Elab Tactic

def _root_.Lean.MVarId.contradiction2 (mvarId : MVarId) : MetaM Unit :=
  unless (← mvarId.contradictionCore (config := { useDecide := false, searchFuel := 0 })) do
    throwTacticEx `contradiction mvarId ""

elab "contradiction2" : tactic => liftMetaTactic fun g => do let _ ← g.contradiction2; pure []

macro "contradiction" : tactic => `(tactic | first | (apply False.elim; assumption) | contradiction2)
