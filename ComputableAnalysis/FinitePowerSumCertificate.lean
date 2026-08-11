import ComputableAnalysis.Series

namespace ComputableAnalysis

/-! Concrete finite power-sum certificates for benchmark item 77. -/

theorem fourthPowerSum_stage6 :
    Series.fourthPowerSum 6 = 979 := by
  native_decide

theorem fifthPowerSum_stage6 :
    Series.fifthPowerSum 6 = 4425 := by
  native_decide

theorem powerSum_stage6_certificate :
    Series.fourthPowerSum 6 = 979 /\
      Series.fifthPowerSum 6 = 4425 := by
  exact ⟨fourthPowerSum_stage6, fifthPowerSum_stage6⟩

theorem eighthPowerSum_stage6 :
    Series.eighthPowerSum 6 = 462979 := by
  native_decide

theorem powerSum_nine_stage6 :
    Series.powerSum 9 6 = 2235465 := by
  native_decide

theorem powerSum_nine_stage8 :
    Series.powerSum 9 8 = 52666768 := by
  native_decide

theorem powerSum_nine_stage10 :
    Series.powerSum 9 10 = 574304985 := by
  native_decide

theorem powerSum_nine_stage12 :
    Series.powerSum 9 12 = 3932252676 := by
  native_decide

theorem powerSum_nine_stage16 :
    Series.powerSum 9 16 = 78800938560 := by
  native_decide

theorem powerSum_nine_stage32 :
    Series.powerSum 9 32 = 95821687265536 := by
  native_decide

theorem powerSum_nine_stage64 :
    Series.powerSum 9 64 = 106496009343230976 := by
  native_decide

theorem powerSum_nine_stage128 :
    Series.powerSum 9 128 = 113501516170343845888 := by
  native_decide

end ComputableAnalysis
