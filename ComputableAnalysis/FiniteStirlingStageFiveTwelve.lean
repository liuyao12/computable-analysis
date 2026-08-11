import ComputableAnalysis.FiniteStirlingCertificate

/-!
# A bounded Stirling-ratio certificate at `n = 512`

This extends the finite rational transport ladder for item 90.  It is a
bounded numerical checkpoint, not an assertion of Stirling's asymptotic limit.
-/

namespace ComputableAnalysis

def finiteStirlingRootApproxFiveTwelve : Rat := 567 / 10

theorem finiteStirlingRootApproxFiveTwelve_squared_bounds :
    (finiteStirlingRootApproxFiveTwelve : Rat) ^ 2 <=
        1024 * finiteStirlingPiInterval.hi /\
      1024 * finiteStirlingPiInterval.lo <=
        (finiteStirlingRootApproxFiveTwelve + 1 / 100) ^ 2 := by
  native_decide

theorem finiteStirlingRatioAtFiveTwelve_enclosure :
    (1 : Rat) / 2 <=
        finiteStirlingRatio 512 finiteStirlingEApprox
          finiteStirlingRootApproxFiveTwelve /\
      finiteStirlingRatio 512 finiteStirlingEApprox
          finiteStirlingRootApproxFiveTwelve <= 2 := by
  native_decide

theorem finiteStirlingRatioAtFiveTwelve_two_percent_enclosure :
    (99 : Rat) / 100 <=
        finiteStirlingRatio 512 finiteStirlingEApprox
          finiteStirlingRootApproxFiveTwelve /\
      finiteStirlingRatio 512 finiteStirlingEApprox
          finiteStirlingRootApproxFiveTwelve <= 102 / 100 := by
  native_decide

theorem finiteStirlingRatioAtFiveTwelve_two_percent_error :
    qabs (finiteStirlingRatio 512 finiteStirlingEApprox
      finiteStirlingRootApproxFiveTwelve - 1) <= 2 / 100 := by
  have h := finiteStirlingRatioAtFiveTwelve_two_percent_enclosure
  apply qabs_le_of_neg_le_le
  · grind [h.1]
  · grind [h.2]

end ComputableAnalysis
