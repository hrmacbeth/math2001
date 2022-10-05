import library.division
import tactic.interval_cases

def int.even (n : ℤ) : Prop := ∃ k, n = 2 * k
def int.odd (n : ℤ) : Prop := ∃ k, n = 2 * k + 1

lemma int.even_or_odd (n : ℤ) : int.even n ∨ int.odd n :=
begin
  obtain ⟨q, r, h, h', hn⟩ := n.exists_quotient_remainder 2 (by norm_num1),
  refine exists_or_distrib.mp ⟨q, _⟩,
  interval_cases r; simp [hn],
end

def nat.even (n : ℕ) : Prop := ∃ k, n = 2 * k
def nat.odd (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

lemma nat.even_or_odd (n : ℕ) : nat.even n ∨ nat.odd n :=
begin
  obtain ⟨q, r, h, hn⟩ := n.exists_quotient_remainder 2 (by norm_num1),
  refine exists_or_distrib.mp ⟨q, _⟩,
  interval_cases r; simp [hn],
end

