import ComputableAnalysis.FiniteStirlingStageEight

/-!
# A third bounded Stirling-ratio certificate

This repeats the finite rational transport at `n = 12`.  It remains a
bounded numerical checkpoint and does not assert Stirling's asymptotic limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxTwelve : Rat := 217 / 25

theorem finiteStirlingRootApproxTwelve_squared_bounds :
    (finiteStirlingRootApproxTwelve : Rat) ^ 2 <=
        24 * finiteStirlingPiInterval.hi /\
      24 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxTwelve + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtTwelve_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 12 finiteStirlingEApprox
          finiteStirlingRootApproxTwelve /\
      finiteStirlingRatio 12 finiteStirlingEApprox
          finiteStirlingRootApproxTwelve <= 2 := by
  native_decide

end ComputableAnalysis
