import data.int.basic
import tactic.congrm
import tactic.linear_combination
import tactic.linarith

-- slightly less concrete form of the division algorithm than mathlib's

lemma int.exists_unique_quotient_remainder' (a b : ℤ) (h : 0 < b) :
  ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ ∃ q : ℤ, r + b * q = a:=
begin
  suffices : ∃! r : ℤ, ∃ q : ℤ, r + b * q = a ∧ 0 ≤ r ∧ r < b,
  { convert this,
    ext r,
    tauto },
  simp_rw ← int.div_mod_unique h,
  tidy,
end

lemma nat.exists_unique_quotient_remainder' (a b : ℕ) (h : 0 < b) :
  ∃! r : ℕ, r < b ∧ ∃ q : ℕ, r + b * q = a:=
begin
  suffices : ∃! r : ℕ, ∃ q : ℕ, r + b * q = a ∧ r < b,
  { convert this,
    ext r,
    tauto },
  simp_rw ← nat.div_mod_unique h,
  tidy,
end

/-- The division algorithm. -/
lemma int.exists_unique_quotient_remainder (a b : ℤ) (h : 0 < b) :
  ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ ∃ q : ℤ, a = b * q + r :=
begin
  convert a.exists_unique_quotient_remainder' b h,
  congrm λ r, _ ∧ _ ∧ ∃ q, _,
  split; rintros rfl; rw add_comm,
end

/-- The division algorithm. -/
lemma nat.exists_unique_quotient_remainder (a b : ℕ) (h : 0 < b) :
  ∃! r : ℕ, r < b ∧ ∃ q : ℕ, a = b * q + r :=
begin
  convert a.exists_unique_quotient_remainder' b h,
  congrm λ r, _ ∧ ∃ q, _,
  split; rintros rfl; rw add_comm,
end

/-- The division algorithm, weak form. -/
lemma int.exists_quotient_remainder (a b : ℤ) (h : 0 < b) :
  ∃ q r : ℤ, 0 ≤ r ∧ r < b ∧ a = b * q + r :=
begin
  obtain ⟨r, ⟨h₁, h₂, q, h₃⟩, -⟩ := int.exists_unique_quotient_remainder a b h,
  exact ⟨q, r, h₁, h₂, h₃⟩,
end

/-- The division algorithm, weak form. -/
lemma nat.exists_quotient_remainder (a b : ℕ) (h : 0 < b) :
  ∃ q r : ℕ, r < b ∧ a = b * q + r :=
begin
  obtain ⟨r, ⟨h₁, q, h₂⟩, -⟩ := nat.exists_unique_quotient_remainder a b h,
  exact ⟨q, r, h₁, h₂⟩,
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

/-- Criterion for a natural number not to divide another. -/
lemma nat.not_dvd_of_exists_lt_and_lt (a : ℕ) {b : ℕ} (hb : 0 < b)
  (h : ∃ q, b * q < a ∧ a < b * (q + 1)) :
  ¬b ∣ a :=
begin
  rintros ⟨q₀, rfl⟩,
  obtain ⟨q, hq₁, hq₂⟩ := h,
  have h₁ : q + 1 ≤ q₀ := lt_of_mul_lt_mul_left hq₁ hb.le,
  have h₂ : q₀ + 1 ≤ q + 1 := lt_of_mul_lt_mul_left hq₂ hb.le,
  linarith,
end