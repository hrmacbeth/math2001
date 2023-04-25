import Mathlib.Data.Set.Basic
import Math2001.Tactic.Define.Attr

-- syntax (name := dsimp) "dsimp" (config)? (discharger)? (&" only")?
--   (" [" withoutPosition((simpErase <|> simpLemma),*) "]")? (location)? : tactic

@[simp] theorem Set.singleton_def' (a : α) : ({a} : Set α) = {b | b = a} := rfl

-- attribute [simp] Set.mem_insert

attribute [set_simps] ne_eq Set.mem_setOf_eq Set.subset_def Set.ext_iff Set.mem_union
  Set.mem_inter_iff Set.mem_compl_iff Set.singleton_def' Set.mem_insert_iff

open Lean.TSyntax.Compat in
macro_rules | `(tactic| dsimp [$t,*] $[$loc:location]?) => `(tactic| simp (config := { decide := false }) only [$t,*, set_simps] $(loc)?)

open Lean.TSyntax.Compat in
macro_rules | `(tactic| dsimp $[$loc:location]?) => `(tactic| simp (config := { decide := false }) only [set_simps] $[$loc]?)

attribute [default_instance] Set.instSingletonSet
attribute [default_instance] Set.instEmptyCollectionSet
-- attribute [-simp] Set.setOf_eq_eq_singleton

-- attribute [default_instance] Set.instInsertSet

-- -- #check Set.mem_insert

-- example (x : Nat) (h : x ∈ {3, 4} ∪ {1,2}) : False := by
--   dsimp at h


-- example (x : Nat) : x ∈ {3, 4} ∪ {1,2} := by
--   dsimp

-- -- def mfld_cfg : Simps.Config where
-- --   attrs := [`mfld_simps]
-- --   fullyApplied := false
-- -- #align mfld_cfg mfld_cfg

-- -- -- namespace Tactic.MfldSetTac

-- -- open Lean Meta Elab Tactic in
-- -- /-- A very basic tactic to show that sets showing up in manifolds coincide or are included
-- -- in one another. -/
-- -- elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
-- --   let g ← getMainGoal
-- --   let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs
-- --   match goalTy with
-- --   | (``Eq, #[_ty, _e₁, _e₂]) =>
-- --     evalTactic (← `(tactic| (
-- --       apply Set.ext; intro my_y
-- --       constructor <;>
-- --         · intro h_my_y
-- --           try (simp only [*, mfld_simps] at h_my_y; simp only [*, mfld_simps]))))
-- --   | (``Subset, #[_ty, _inst, _e₁, _e₂]) =>
-- --     evalTactic (← `(tactic| (
-- --       intro my_y h_my_y
-- --       try (simp only [*, mfld_simps] at h_my_y; simp only [*, mfld_simps]))))
-- --   | _ => throwError "goal should be an equality or an inclusion"

-- -- macro_rules | `(tactic| dsimp [$t,*]) => `(tactic| simp only [$t,*] using set_simps)

-- -- macro_rules | `(tactic| rel [$t,*]) => `(tactic| ineq_rel [$t,*])

-- -- macro_rules
-- -- | `(tactic| simple_induction $tgts,* $[with $withArg*]?) =>
-- --     `(tactic| induction' $tgts,* using Nat.induction $[with $withArg*]? <;>
-- --       push_cast (config := { decide := false }))
