import Mathlib.Data.Nat.Factorial.Basic

open Nat

theorem Nat.factorial_succ' (n : ℕ) : (n + 1)! = (n + 1) * n ! := factorial_succ n
