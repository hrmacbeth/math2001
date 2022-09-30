import data.int.basic
import tactic.congrm
import tactic.linear_combination
import tactic.linarith

-- slightly less concrete form of the division algorithm than mathlib's

lemma int.exists_unique_quotient_remainder' (a b : ℤ) (h : 0 < b) :
  ∃! p : ℤ × ℤ, p.2 + b * p.1 = a ∧ 0 ≤ p.2 ∧ p.2 < b :=
begin
  simp only [← int.div_mod_unique h, exists_unique, prod.exists],
  tidy,
end

/-- The division algorithm. -/
lemma int.exists_unique_quotient_remainder (a b : ℤ) (h : 0 < b) :
  ∃! p : ℤ × ℤ, a = b * p.1 + p.2 ∧ 0 ≤ p.2 ∧ p.2 < b :=
begin
  convert a.exists_unique_quotient_remainder' b h,
  congrm λ p, _ ∧ _ ∧ _,
  split; intros h; linear_combination -h
end

/-- The division algorithm, weak form. -/
lemma int.exists_quotient_remainder (a b : ℤ) (h : 0 < b) :
  ∃ q r : ℤ, a = b * q + r ∧ 0 ≤ r ∧ r < b :=
begin
  obtain ⟨⟨q, r⟩, h, -⟩ := int.exists_unique_quotient_remainder a b h,
  use ⟨q, r, h⟩,
end

/-- Criterion for an integer not to divide another. -/
lemma int.not_dvd_of_exists_lt_and_lt (a : ℤ) {b : ℤ} (hb : 0 < b)
  (h : ∃ q, b * q < a ∧ a < b * (q + 1)) :
  ¬b ∣ a :=
begin
  rintros ⟨q₀, rfl⟩,
  obtain ⟨q, hq₁, hq₂⟩ := h,
  have h₁ : q + 1 ≤ q₀ := lt_of_mul_lt_mul_left hq₁ hb.le,
  have h₂ : q₀ + 1 ≤ q + 1 := lt_of_mul_lt_mul_left hq₂ hb.le,
  linarith,
end