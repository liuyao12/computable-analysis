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

end ComputableAnalysis
