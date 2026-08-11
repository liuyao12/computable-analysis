import ComputableAnalysis.FiniteStirlingStageSixteen

/-!
# A fifth bounded Stirling-ratio certificate

This repeats the finite rational transport at `n = 20`.  It is a bounded
numerical checkpoint for item 90, not an assertion of Stirling's asymptotic
limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxTwenty : Rat := 1121 / 100

theorem finiteStirlingRootApproxTwenty_squared_bounds :
    (finiteStirlingRootApproxTwenty : Rat) ^ 2 <=
        40 * finiteStirlingPiInterval.hi /\
      40 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxTwenty + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtTwenty_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 20 finiteStirlingEApprox
          finiteStirlingRootApproxTwenty /\
      finiteStirlingRatio 20 finiteStirlingEApprox
          finiteStirlingRootApproxTwenty <= 2 := by
  native_decide

end ComputableAnalysis
