import ComputableAnalysis.Series

/-!
# A worked reciprocal triangular-number certificate

At stage four, the finite sum is `1 + 1/3 + 1/6 + 1/10 = 8/5`, and its
remaining gap to the potential limit `2` is `2/5`.  The example records both
the exact telescoping value and the finite tail budget.
-/

namespace ComputableAnalysis

theorem triangular_stage4_sum :
    Series.triangularTelescopingSum 4 = 8 / 5 := by
  native_decide

theorem triangular_stage4_tail :
    2 - Series.triangularTelescopingSum 4 = 2 / 5 := by
  rw [triangular_stage4_sum]
  native_decide

theorem triangular_stage4_certificate :
    Series.triangularTelescopingSum 4 < 2 /\
      2 - Series.triangularTelescopingSum 4 = 2 / 5 := by
  exact ⟨by rw [triangular_stage4_sum]; native_decide,
    triangular_stage4_tail⟩

theorem triangular_stage8_sum :
    Series.triangularTelescopingSum 8 = 16 / 9 := by
  native_decide

theorem triangular_stage8_tail :
    2 - Series.triangularTelescopingSum 8 = 2 / 9 := by
  rw [triangular_stage8_sum]
  native_decide

theorem triangular_stage8_certificate :
    Series.triangularTelescopingSum 8 < 2 /\
      2 - Series.triangularTelescopingSum 8 = 2 / 9 := by
  exact ⟨by rw [triangular_stage8_sum]; native_decide,
    triangular_stage8_tail⟩

theorem triangular_stage16_sum :
    Series.triangularTelescopingSum 16 = 32 / 17 := by
  native_decide

theorem triangular_stage16_tail :
    2 - Series.triangularTelescopingSum 16 = 2 / 17 := by
  rw [triangular_stage16_sum]
  native_decide

theorem triangular_stage16_certificate :
    Series.triangularTelescopingSum 16 < 2 /\
      2 - Series.triangularTelescopingSum 16 = 2 / 17 := by
  exact ⟨by rw [triangular_stage16_sum]; native_decide,
    triangular_stage16_tail⟩

theorem triangular_stage32_sum :
    Series.triangularTelescopingSum 32 = 64 / 33 := by
  native_decide

theorem triangular_stage32_tail :
    2 - Series.triangularTelescopingSum 32 = 2 / 33 := by
  rw [triangular_stage32_sum]
  native_decide

theorem triangular_stage32_certificate :
    Series.triangularTelescopingSum 32 < 2 /\
      2 - Series.triangularTelescopingSum 32 = 2 / 33 := by
  exact ⟨by rw [triangular_stage32_sum]; native_decide,
    triangular_stage32_tail⟩

theorem triangular_stage64_sum :
    Series.triangularTelescopingSum 64 = 128 / 65 := by
  rw [Series.triangularTelescopingSum_eq]
  native_decide

theorem triangular_stage64_tail :
    2 - Series.triangularTelescopingSum 64 = 2 / 65 := by
  rw [triangular_stage64_sum]
  native_decide

theorem triangular_stage64_certificate :
    Series.triangularTelescopingSum 64 < 2 /\
      2 - Series.triangularTelescopingSum 64 = 2 / 65 := by
  exact ⟨by rw [triangular_stage64_sum]; native_decide,
    triangular_stage64_tail⟩

end ComputableAnalysis
