import ComputableAnalysis.FiniteStirlingStageSixteen

/-!
# An eighth bounded Stirling-ratio certificate

This extends the finite rational transport to `n = 64`.  It is a bounded
numerical checkpoint for item 90, not an assertion of Stirling's asymptotic
limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxSixtyFour : Rat := 2005 / 100

theorem finiteStirlingRootApproxSixtyFour_squared_bounds :
    (finiteStirlingRootApproxSixtyFour : Rat) ^ 2 <=
        128 * finiteStirlingPiInterval.hi /\
      128 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxSixtyFour + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtSixtyFour_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 64 finiteStirlingEApprox
          finiteStirlingRootApproxSixtyFour /\
      finiteStirlingRatio 64 finiteStirlingEApprox
          finiteStirlingRootApproxSixtyFour <= 2 := by
  native_decide

end ComputableAnalysis
