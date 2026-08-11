import ComputableAnalysis.FiniteStirlingStageSixteen

/-!
# A sixth bounded Stirling-ratio certificate

This repeats the finite rational transport at `n = 24`.  It is a bounded
numerical checkpoint for item 90, not an assertion of Stirling's asymptotic
limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxTwentyFour : Rat := 12279 / 1000

theorem finiteStirlingRootApproxTwentyFour_squared_bounds :
    (finiteStirlingRootApproxTwentyFour : Rat) ^ 2 <=
        48 * finiteStirlingPiInterval.hi /\
      48 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxTwentyFour + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtTwentyFour_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 24 finiteStirlingEApprox
          finiteStirlingRootApproxTwentyFour /\
      finiteStirlingRatio 24 finiteStirlingEApprox
          finiteStirlingRootApproxTwentyFour <= 2 := by
  native_decide

end ComputableAnalysis
