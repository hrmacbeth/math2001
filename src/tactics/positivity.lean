import tactic.positivity

open tactic tactic.positivity

-- in mathlib PR #16141
/-- Second base case of the `positivity` tactic: Any element of a canonically ordered additive
monoid is nonnegative. -/
@[positivity]
meta def positivity_canon : expr → tactic strictness
| `(%%a) := nonnegative <$> mk_app ``zero_le [a]
