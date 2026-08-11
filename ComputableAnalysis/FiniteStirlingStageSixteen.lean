import ComputableAnalysis.FiniteStirlingStageEight

/-!
# A fourth bounded Stirling-ratio certificate

This repeats the finite rational transport at `n = 16`.  It remains a broad
bounded numerical checkpoint and does not assert Stirling's asymptotic limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxSixteen : Rat := 1003 / 100

theorem finiteStirlingRootApproxSixteen_squared_bounds :
    (finiteStirlingRootApproxSixteen : Rat) ^ 2 <=
        32 * finiteStirlingPiInterval.hi /\
      32 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxSixteen + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtSixteen_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 16 finiteStirlingEApprox
          finiteStirlingRootApproxSixteen /\
      finiteStirlingRatio 16 finiteStirlingEApprox
          finiteStirlingRootApproxSixteen <= 2 := by
  native_decide

end ComputableAnalysis
