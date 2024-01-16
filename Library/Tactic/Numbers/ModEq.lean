/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Theory.ModEq.Defs
import Mathlib.Tactic.Linarith

open Lean hiding Rat mkRat
open Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Meta.NormNum

theorem isInt_ModEq_true : (a b n : ℤ) → decide (a = b) = true →
    Int.ModEq n a b
  | a, b, n, hab =>
    by
      replace hab := of_decide_eq_true hab
      rw [hab]
      use 0
      ring

theorem isInt_ModEq_false : (a b n : ℤ) → decide (0 < n) = true →
    decide (a < n) = true → decide (b < n) = true → decide (0 ≤ a) = true →
    decide (0 ≤ b) = true → decide (a ≠ b) = true → ¬ Int.ModEq n a b
  | a, b, n, hn, han, hbn, ha, hb, hab =>
    by
      change ¬ n ∣ _
      replace hn := of_decide_eq_true hn
      replace han := of_decide_eq_true han
      replace hbn := of_decide_eq_true hbn
      replace ha := of_decide_eq_true ha
      replace hb := of_decide_eq_true hb
      replace hab := of_decide_eq_true hab
      rw [← Int.exists_lt_and_lt_iff_not_dvd _ hn]
      cases' lt_or_gt_of_ne hab with hab hab
      · exact ⟨-1, by linarith, by linarith⟩
      · exact ⟨0, by linarith, by linarith⟩

end Mathlib.Meta.NormNum

/-- The `norm_num` extension which identifies expressions of the form `a ≡ b [ZMOD n]`,
such that `norm_num` successfully recognises both `a` and `b` and they are small compared to `n`. -/
@[norm_num Int.ModEq _ _ _] def evalModEq : NormNumExt where eval (e : Q(Prop)) := do
  let .app (.app (.app f (n : Q(ℤ))) (a : Q(ℤ))) (b : Q(ℤ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq f q(Int.ModEq)
  let ra : Result a ← derive a
  let rb : Result b ← derive b
  let rn : Result n ← derive n
  let i : Q(Ring ℤ) := q(Int.instRingInt)
  let ⟨za, _, _⟩ ← ra.toInt
  let ⟨zb, _, _⟩ ← rb.toInt
  let ⟨zn, _, _⟩ ← rn.toInt i
  if za = zb then
    -- reduce `a ≡ b [ZMOD n]` to `true` if `a` and `b` reduce to the same integer
    haveI' pab : decide ($a = $b) =Q true := ⟨⟩
    let r : Q(Int.ModEq $n $a $b) := q(isInt_ModEq_true $a $b $n $pab)
    return Result.isTrue r
  else
    -- reduce `a ≡ b [ZMOD n]` to `false` if `0 < n`, `a` reduces to `a'` with `0 ≤ a' < n`,
    -- and `b` reduces to `b'` with `0 ≤ b' < n`
    haveI' pab : decide ($a ≠ $b) =Q true := ⟨⟩
    if zn = 0 then failure
    haveI' pn : decide (0 < $n) =Q true := ⟨⟩
    if zn ≤ za then failure
    haveI' pan : decide ($a < $n) =Q true := ⟨⟩
    if zn ≤ zb then failure
    haveI' pbn : decide ($b < $n) =Q true := ⟨⟩
    if za < 0 then failure
    haveI' pa0 : decide (0 ≤ $a) =Q true := ⟨⟩
    if zb < 0 then failure
    haveI' pb0 : decide (0 ≤ $b) =Q true := ⟨⟩
    assumeInstancesCommute
    have r : Q(¬Int.ModEq $n $a $b) := q(isInt_ModEq_false $a $b $n $pn $pan $pbn $pa0 $pb0 $pab)
    return Result.isFalse r
