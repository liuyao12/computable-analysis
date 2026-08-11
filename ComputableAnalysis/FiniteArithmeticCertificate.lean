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

theorem arithmeticProgression_3_2_stage10_sum :
    Series.arithmeticProgressionSum 3 2 10 = 120 := by
  native_decide

theorem arithmeticProgression_3_2_stage10_closed_form :
    Series.arithmeticProgressionSum 3 2 10 =
      (10 : Rat) * (2 * 3 + ((10 : Rat) - 1) * 2) / 2 := by
  rw [Series.arithmeticProgressionSum_eq]
  native_decide

theorem arithmeticProgression_3_2_stage10_certificate :
    Series.arithmeticProgressionSum 3 2 10 = 120 /\
      Series.arithmeticProgressionSum 3 2 10 <= 121 := by
  constructor
  · exact arithmeticProgression_3_2_stage10_sum
  · rw [arithmeticProgression_3_2_stage10_sum]
    native_decide

theorem arithmeticProgression_3_2_stage20_sum :
    Series.arithmeticProgressionSum 3 2 20 = 440 := by
  native_decide

theorem arithmeticProgression_3_2_stage20_closed_form :
    Series.arithmeticProgressionSum 3 2 20 =
      (20 : Rat) * (2 * 3 + ((20 : Rat) - 1) * 2) / 2 := by
  rw [Series.arithmeticProgressionSum_eq]
  native_decide

theorem arithmeticProgression_3_2_stage20_certificate :
    Series.arithmeticProgressionSum 3 2 20 = 440 /\
      Series.arithmeticProgressionSum 3 2 20 <= 441 := by
  constructor
  · exact arithmeticProgression_3_2_stage20_sum
  · rw [arithmeticProgression_3_2_stage20_sum]
    native_decide

theorem arithmeticProgression_3_2_stage40_sum :
    Series.arithmeticProgressionSum 3 2 40 = 1680 := by
  native_decide

theorem arithmeticProgression_3_2_stage40_closed_form :
    Series.arithmeticProgressionSum 3 2 40 =
      (40 : Rat) * (2 * 3 + ((40 : Rat) - 1) * 2) / 2 := by
  rw [Series.arithmeticProgressionSum_eq]
  native_decide

theorem arithmeticProgression_3_2_stage40_certificate :
    Series.arithmeticProgressionSum 3 2 40 = 1680 /\
      Series.arithmeticProgressionSum 3 2 40 <= 1681 := by
  constructor
  · exact arithmeticProgression_3_2_stage40_sum
  · rw [arithmeticProgression_3_2_stage40_sum]
    native_decide

theorem arithmeticProgression_3_2_stage80_sum :
    Series.arithmeticProgressionSum 3 2 80 = 6560 := by
  native_decide

theorem arithmeticProgression_3_2_stage80_closed_form :
    Series.arithmeticProgressionSum 3 2 80 =
      (80 : Rat) * (2 * 3 + ((80 : Rat) - 1) * 2) / 2 := by
  rw [Series.arithmeticProgressionSum_eq]
  native_decide

theorem arithmeticProgression_3_2_stage80_certificate :
    Series.arithmeticProgressionSum 3 2 80 = 6560 /\
      Series.arithmeticProgressionSum 3 2 80 <= 6561 := by
  constructor
  · exact arithmeticProgression_3_2_stage80_sum
  · rw [arithmeticProgression_3_2_stage80_sum]
    native_decide

theorem arithmeticProgression_3_2_stage160_sum :
    Series.arithmeticProgressionSum 3 2 160 = 25920 := by
  native_decide

theorem arithmeticProgression_3_2_stage160_closed_form :
    Series.arithmeticProgressionSum 3 2 160 =
      (160 : Rat) * (2 * 3 + ((160 : Rat) - 1) * 2) / 2 := by
  rw [Series.arithmeticProgressionSum_eq]
  native_decide

theorem arithmeticProgression_3_2_stage160_certificate :
    Series.arithmeticProgressionSum 3 2 160 = 25920 /\
      Series.arithmeticProgressionSum 3 2 160 <= 25921 := by
  constructor
  · exact arithmeticProgression_3_2_stage160_sum
  · rw [arithmeticProgression_3_2_stage160_sum]
    native_decide

theorem arithmeticProgression_3_2_stage320_sum :
    Series.arithmeticProgressionSum 3 2 320 = 103040 := by
  native_decide

theorem arithmeticProgression_3_2_stage320_closed_form :
    Series.arithmeticProgressionSum 3 2 320 =
      (320 : Rat) * (2 * 3 + ((320 : Rat) - 1) * 2) / 2 := by
  rw [Series.arithmeticProgressionSum_eq]
  native_decide

theorem arithmeticProgression_3_2_stage320_certificate :
    Series.arithmeticProgressionSum 3 2 320 = 103040 /\
      Series.arithmeticProgressionSum 3 2 320 <= 103041 := by
  constructor
  · exact arithmeticProgression_3_2_stage320_sum
  · rw [arithmeticProgression_3_2_stage320_sum]
    native_decide

theorem arithmeticProgression_3_2_stage640_sum :
    Series.arithmeticProgressionSum 3 2 640 = 410880 := by
  native_decide

theorem arithmeticProgression_3_2_stage640_closed_form :
    Series.arithmeticProgressionSum 3 2 640 =
      (640 : Rat) * (2 * 3 + ((640 : Rat) - 1) * 2) / 2 := by
  rw [Series.arithmeticProgressionSum_eq]
  native_decide

theorem arithmeticProgression_3_2_stage640_certificate :
    Series.arithmeticProgressionSum 3 2 640 = 410880 /\
      Series.arithmeticProgressionSum 3 2 640 <= 410881 := by
  constructor
  · exact arithmeticProgression_3_2_stage640_sum
  · rw [arithmeticProgression_3_2_stage640_sum]
    native_decide

end ComputableAnalysis
