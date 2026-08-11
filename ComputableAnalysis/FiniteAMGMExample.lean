import ComputableAnalysis.FiniteDyadicAMGM

namespace ComputableAnalysis

/-! Concrete finite AM--GM certificates for benchmark item 38. -/

theorem amgm_2_8_certificate :
    (2 : Rat) * 8 <= ((2 + 8) / 2) ^ 2 := by
  native_decide

theorem amgm_3_3_equality :
    ((3 : Rat) * 3) = ((3 + 3) / 2) ^ 2 := by
  native_decide

theorem amgm_2_8_and_equality_certificate :
    (2 : Rat) * 8 <= ((2 + 8) / 2) ^ 2 /\
      ((3 : Rat) * 3) = ((3 + 3) / 2) ^ 2 := by
  exact ⟨amgm_2_8_certificate, amgm_3_3_equality⟩

theorem amgm_four_equal_certificate :
    (3 : Rat) * 3 * 3 * 3 = ((3 + 3 + 3 + 3) / 4) ^ 4 := by
  native_decide

theorem amgm_four_strict_certificate :
    (2 : Rat) * 3 * 4 * 5 < ((2 + 3 + 4 + 5) / 4) ^ 4 := by
  native_decide

theorem amgm_four_certificate :
    (3 : Rat) * 3 * 3 * 3 = ((3 + 3 + 3 + 3) / 4) ^ 4 /\
      (2 : Rat) * 3 * 4 * 5 < ((2 + 3 + 4 + 5) / 4) ^ 4 := by
  exact ⟨amgm_four_equal_certificate, amgm_four_strict_certificate⟩

end ComputableAnalysis
