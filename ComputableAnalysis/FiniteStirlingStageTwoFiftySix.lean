import ComputableAnalysis.FiniteStirlingStageOneTwentyEight

/-!
# A tenth bounded Stirling-ratio certificate

This extends the finite rational transport to `n = 256`.  It is a bounded
numerical checkpoint for item 90, not an assertion of Stirling's asymptotic
limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxTwoFiftySix : Rat := 401 / 10

theorem finiteStirlingRootApproxTwoFiftySix_squared_bounds :
    (finiteStirlingRootApproxTwoFiftySix : Rat) ^ 2 <=
        512 * finiteStirlingPiInterval.hi /\
      512 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxTwoFiftySix + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtTwoFiftySix_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 256 finiteStirlingEApprox
          finiteStirlingRootApproxTwoFiftySix /\
      finiteStirlingRatio 256 finiteStirlingEApprox
          finiteStirlingRootApproxTwoFiftySix <= 2 := by
  native_decide

end ComputableAnalysis
