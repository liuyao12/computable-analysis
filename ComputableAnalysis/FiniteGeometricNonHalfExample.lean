import ComputableAnalysis.Series

namespace ComputableAnalysis

/-! A non-half-ratio geometric certificate.  This keeps the finite-series
interface tied to the general rational ratio rather than only its simplest
`1/2` instance. -/

theorem geometricThird_stage6_sum :
    Series.geometricSum ((1 : Rat) / 3) 6 = 364 / 243 := by
  native_decide

theorem geometricThird_stage6_tail :
    (3 : Rat) / 2 - Series.geometricSum ((1 : Rat) / 3) 6 = 1 / 486 := by
  rw [geometricThird_stage6_sum]
  native_decide

theorem geometricThird_stage6_enclosure :
    Series.geometricSum ((1 : Rat) / 3) 6 <= (3 : Rat) / 2 /\
      (3 : Rat) / 2 - Series.geometricSum ((1 : Rat) / 3) 6 <= 1 / 486 := by
  constructor
  · rw [geometricThird_stage6_sum]
    native_decide
  · rw [geometricThird_stage6_tail]
    native_decide

end ComputableAnalysis
