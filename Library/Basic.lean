import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.ExistsDelaborator
import Library.Tactic.Extra.Basic
import Library.Tactic.Induction
import Library.Tactic.Numbers.Basic
import Library.Tactic.Product
import Library.Tactic.Rel
import Library.Tactic.Set
import Library.Tactic.TruthTable
import Library.Tactic.Use

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
