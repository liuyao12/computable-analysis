import ComputableAnalysis.FiniteStirlingCertificate

/-!
# A second bounded Stirling-ratio certificate

The same finite rational inputs are reused at the concrete index `n = 8`,
with a separate square-root bracket for `sqrt (16*pi)`.  This remains a
bounded numerical exercise, not an asymptotic statement.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxEight : Rat := 709 / 100

theorem finiteStirlingRootApproxEight_squared_bounds :
    (finiteStirlingRootApproxEight : Rat) ^ 2 <=
        16 * finiteStirlingPiInterval.hi ∧
      16 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxEight + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtEight_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 8 finiteStirlingEApprox
          finiteStirlingRootApproxEight ∧
      finiteStirlingRatio 8 finiteStirlingEApprox
          finiteStirlingRootApproxEight <= 2 := by
  native_decide

end ComputableAnalysis
