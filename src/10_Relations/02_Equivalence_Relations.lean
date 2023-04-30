/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Math2001.Library.Parity
import Math2001.Tactic.Addarith
import Math2001.Tactic.ExistsDelaborator
import Math2001.Tactic.Numbers
import Math2001.Tactic.Rel
import Math2001.Tactic.Take

set_option push_neg.use_distrib true
set_option linter.unusedVariables false
set_option quotPrecheck false
macro_rules | `(tactic| ring) => `(tactic| ring_nf <;> with_reducible exact trivial)


section
variable (n : ℤ)

local infix:50 "∼" => fun (x y : ℤ) ↦ x ≡ y [ZMOD n]

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  apply Int.ModEq.refl

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  apply Int.ModEq.symm

example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  apply Int.ModEq.trans

end


section

local infix:50 "∼" => fun (x y : ℤ) ↦ x ^ 2 = y ^ 2

example : Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  intro x
  ring

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intro x y hxy
  rw [hxy]

example : Transitive (· ∼ ·) := by
  dsimp [Transitive]
  intro x y z hxy hyz
  rw [hxy, hyz]

end



/-! # Exercises -/


section
local infix:50 "∼" => fun (a b : ℤ) ↦ ∃ m n, m > 0 ∧ n > 0 ∧ a * m = b * n  

example : Reflexive (· ∼ ·) := by
  sorry

example : Symmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

end


section
local infix:50 "∼" => fun ((a, b) : ℕ × ℕ) (c, d) ↦ a + d = b + c

example : Reflexive (· ∼ ·) := by
  sorry

example : Symmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

end


section
local infix:50 "∼" => fun ((a, b) : ℤ × ℤ) (c, d) ↦ ∃ m n, m > 0 ∧ n > 0 ∧ m * b * (b ^ 2 - 3 * a ^ 2) = n * d * (d ^ 2 - 3 * c ^ 2)

example : Reflexive (· ∼ ·) := by
  sorry

example : Symmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

end