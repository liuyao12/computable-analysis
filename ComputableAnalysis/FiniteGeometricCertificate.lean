import ComputableAnalysis.Series

namespace ComputableAnalysis

/-! A concrete finite certificate for the geometric-series benchmark.
The ratio `1/2` is evaluated at a finite stage, and the exact tail is retained
as a rational error budget.
-/

theorem geometricHalf_stage5_sum :
    Series.geometricSum ((1 : Rat) / 2) 5 = 31 / 16 := by
  native_decide

theorem geometricHalf_stage5_tail :
    2 - Series.geometricSum ((1 : Rat) / 2) 5 = 1 / 16 := by
  rw [geometricHalf_stage5_sum]
  native_decide

theorem geometricHalf_stage5_enclosure :
    Series.geometricSum ((1 : Rat) / 2) 5 <= 2 /\
      2 - Series.geometricSum ((1 : Rat) / 2) 5 <= 1 / 16 := by
  constructor
  · rw [geometricHalf_stage5_sum]
    native_decide
  · rw [geometricHalf_stage5_tail]
    native_decide

end ComputableAnalysis
