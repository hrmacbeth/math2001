import Math2001.Library.Parity
import Math2001.Library.ModEq.Defs

theorem Int.odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by linear_combination hk⟩

theorem Int.even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor <;> rintro ⟨k, hk⟩ <;> exact ⟨k, by linear_combination hk⟩
