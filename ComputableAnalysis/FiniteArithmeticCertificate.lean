import ComputableAnalysis.Series

namespace ComputableAnalysis

/-! A concrete finite arithmetic-progression certificate for benchmark item 68. -/

theorem arithmeticProgression_3_2_stage5_sum :
    Series.arithmeticProgressionSum 3 2 5 = 35 := by
  native_decide

theorem arithmeticProgression_3_2_stage5_closed_form :
    Series.arithmeticProgressionSum 3 2 5 =
      (5 : Rat) * (2 * 3 + ((5 : Rat) - 1) * 2) / 2 := by
  rw [Series.arithmeticProgressionSum_eq]
  native_decide

theorem arithmeticProgression_3_2_stage5_certificate :
    Series.arithmeticProgressionSum 3 2 5 = 35 /\
      Series.arithmeticProgressionSum 3 2 5 <= 36 := by
  constructor
  · exact arithmeticProgression_3_2_stage5_sum
  · rw [arithmeticProgression_3_2_stage5_sum]
    native_decide

end ComputableAnalysis
