import data.int.basic
import tactic.congrm
import tactic.linear_combination

-- slightly less concrete form of the division algorithm than mathlib's

lemma int.exists_unique_quotient_remainder' (a b : ℤ) (h : 0 < b) :
  ∃! q r : ℤ, r + b * q = a ∧ 0 ≤ r ∧ r < b :=
begin
  simp only [← int.div_mod_unique h, exists_unique],
  tidy,
end

/-- The division algorithm. -/
lemma int.exists_unique_quotient_remainder (a b : ℤ) (h : 0 < b) :
  ∃! q r : ℤ, a = b * q + r ∧ 0 ≤ r ∧ r < b :=
begin
  convert a.exists_unique_quotient_remainder' b h,
  congrm λ q, ∃! r, _ ∧ _ ∧ _,
  split; intros h; linear_combination -h
end