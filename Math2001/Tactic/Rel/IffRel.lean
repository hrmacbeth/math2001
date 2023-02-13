/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Math2001.Tactic.Rel.Basic

open Lean Elab Tactic

def introProc (_ : List MVarId) (curr : List MVarId) : MetaM (Option (List MVarId)) :=
  some <$> curr.mapM (fun mvarId => Prod.snd <$> mvarId.intro `_) <|> pure none

syntax (name := IffRelSyntax) "iff_rel" " [" term,* "] " : tactic

elab_rules : tactic | `(tactic| iff_rel [$t,*]) => do
  liftMetaTactic <|
    Lean.MVarId.Rel `iff_rules t.getElems.toList
      "cannot prove this by 'substituting' the listed relationships"
      (proc := introProc)

macro_rules | `(tactic| rel [$t,*]) => `(tactic| iff_rel [$t,*])

attribute [iff_rules]
  Iff.refl
  not_congr
  and_congr_left and_congr_right and_congr
  or_congr_left or_congr_right or_congr
  imp_congr
  iff_congr
  exists_congr forall_congr'