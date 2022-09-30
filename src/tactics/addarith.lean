import tactic.abel
import tactic.linarith

namespace tactic

meta def norm_num1' : tactic unit := norm_num1 (norm_num.derive.step) (interactive.loc.ns [none])

meta def abel_aux : tactic unit := do
  success ← replace_at (abel.normalize semireducible abel.normalize_mode.term) [] tt,
  pure ()

namespace interactive

setup_tactic_parser

-- This tactic is a deliberately weakened version of the mathlib tactic `linarith`.
meta def addarith (hyp : parse parser.pexpr) : tactic unit :=
tactic.linarith ff tt [hyp]
{ discharger := `[try { simp only [one_mul, neg_mul] }, abel_aux, try { simp only [zsmul_eq_mul] }, try { push_cast }, norm_num1'] }

/-
Note: `addarith` fails in an unprincipled way on some goals with more than one hypothesis, e.g.
because of the main linarith tactic turning (a + a)'s into (2a)'s.  For example,

example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
by addarith [h1, h2]

example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) (h3 : x + x = 2 * x) : 
  x = 5 :=
by addarith [h1, h2, h3]

-/

end interactive

end tactic