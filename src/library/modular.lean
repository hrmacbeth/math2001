/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/

import data.int.modeq

-- lemma int.even_iff_modeq (n : ℤ) : even n ↔ n ≡ 0 [ZMOD 2] :=
-- begin
--   rw int.modeq_zero_iff_dvd,
--   exact even_iff_two_dvd
-- end

-- lemma int.odd_iff_modeq (n : ℤ) : odd n ↔ n ≡ 1 [ZMOD 2] :=
-- begin
--   rw int.modeq_iff_dvd,
--   split,
--   { rintros ⟨a, rfl⟩,
--     refine ⟨-a, by ring⟩ },
--   { rintros ⟨a, ha⟩,
--     refine ⟨-a, _⟩,
--     simp [← ha] },
-- end

theorem int.modeq_add_fac' {a n : ℤ} (c : ℤ) : a + n*c ≡ a [ZMOD n] :=
calc a + n*c ≡ a + 0 [ZMOD n] : (dvd_mul_right _ _).modeq_zero_int.add_left _
         ... ≡ a [ZMOD n] : by rw add_zero

-- prevents `int.modeq` facts from being true by definition
attribute [irreducible] int.modeq
