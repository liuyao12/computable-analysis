import MathlibComparison.CosinePrimitive

/-! A calibration case for the reusable comparison suite. This optional proof
uses the independently established sine representation, not native S_zero. -/
namespace MathlibComparison.ProofBenchExamples
open ComputableAnalysis CosinePrimitive

theorem sine_zero_viaMathlib : (S 0).Equiv RealRaw.zero := by
  have hzero : Domain 0 := by constructor <;> decide +kernel
  have hs : Represents (S 0) (0 : ℝ) := by
    have h := sine_represents ClosedArctanInverse.provider 0 hzero
    simpa only [S, CosineFTC.sine, dif_pos hzero, Rat.cast_zero,
      mul_zero, Real.sin_zero] using h
  have hz : Represents RealRaw.zero (0 : ℝ) := by
    simpa only [RealRaw.zero, Rat.cast_zero] using represents_rat (0 : Rat)
  exact equiv_of_represents hs hz

end MathlibComparison.ProofBenchExamples
