/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

/-! # Homework 0

Don't forget to compare with the text version,
https://hrmacbeth.github.io/math2001/Homework.html#homework-0
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  sorry
