import ComputableAnalysis.FiniteStirlingStageSixteen

/-!
# A ninth bounded Stirling-ratio certificate

This extends the finite rational transport to `n = 128`.  It is a bounded
numerical checkpoint for item 90, not an assertion of Stirling's asymptotic
limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxOneTwentyEight : Rat := 2836 / 100

theorem finiteStirlingRootApproxOneTwentyEight_squared_bounds :
    (finiteStirlingRootApproxOneTwentyEight : Rat) ^ 2 <=
        256 * finiteStirlingPiInterval.hi /\
      256 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxOneTwentyEight + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtOneTwentyEight_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 128 finiteStirlingEApprox
          finiteStirlingRootApproxOneTwentyEight /\
      finiteStirlingRatio 128 finiteStirlingEApprox
          finiteStirlingRootApproxOneTwentyEight <= 2 := by
  native_decide

end ComputableAnalysis
