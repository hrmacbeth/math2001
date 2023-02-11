import Mathlib.Tactic.LeftRight
import Mathlib.Tactic.Have
import Math2001.Tactic.TruthTable


example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction  


example {P Q : Prop} : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP


#truth_table ¬(P ∧ ¬ Q)


example {P : Prop} : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example {P Q R : Prop} : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · sorry

#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  sorry

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  sorry

example {P : Prop} : ¬(P ∧ ¬ P) := by
  sorry

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  sorry

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  sorry

example {P : Prop} : (P ∧ P) ↔ P := by
  sorry

example {P Q : Prop} : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  sorry
