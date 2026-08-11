import ComputableAnalysis.FiniteStirlingStageSixteen

/-!
# A seventh bounded Stirling-ratio certificate

This repeats the finite rational transport at `n = 32`.  It is a bounded
numerical checkpoint for item 90, not an assertion of Stirling's asymptotic
limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxThirtyTwo : Rat := 1418 / 100

theorem finiteStirlingRootApproxThirtyTwo_squared_bounds :
    (finiteStirlingRootApproxThirtyTwo : Rat) ^ 2 <=
        64 * finiteStirlingPiInterval.hi /\
      64 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxThirtyTwo + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtThirtyTwo_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 32 finiteStirlingEApprox
          finiteStirlingRootApproxThirtyTwo /\
      finiteStirlingRatio 32 finiteStirlingEApprox
          finiteStirlingRootApproxThirtyTwo <= 2 := by
  native_decide

end ComputableAnalysis
