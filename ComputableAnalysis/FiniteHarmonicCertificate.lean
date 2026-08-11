import ComputableAnalysis.Logarithm

namespace ComputableAnalysis

/-! A concrete finite witness for harmonic-series growth (benchmark item 34). -/

theorem harmonicSum_stage8_exact :
    Logarithm.harmonicSum 8 = 761 / 280 := by
  native_decide

theorem harmonicSum_stage8_exceeds_two :
    (2 : Rat) <= Logarithm.harmonicSum 8 := by
  rw [harmonicSum_stage8_exact]
  native_decide

theorem harmonicSum_stage8_certificate :
    Logarithm.harmonicSum 8 = 761 / 280 /\
      (2 : Rat) <= Logarithm.harmonicSum 8 := by
  exact ⟨harmonicSum_stage8_exact, harmonicSum_stage8_exceeds_two⟩

end ComputableAnalysis
