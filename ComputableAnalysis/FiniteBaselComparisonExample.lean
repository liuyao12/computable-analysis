import ComputableAnalysis.BaselFiniteComparison

/-!
# A named finite Basel comparison witness

The midpoint of the common stage-10000/stage-8 interval is exported as a
reusable rational witness lying in both independent enclosures.  This is a
finite cross-check, not a proof of Euler's Basel identity.
-/

namespace ComputableAnalysis

namespace BaselFiniteComparison

def baselPartialExample : Rat := DirichletSeries.zetaTwoPartial 8

theorem baselPartialExample_exact :
    baselPartialExample = (1077749 : Rat) / 705600 := by
  native_decide

theorem baselPartialExample_positive_and_below_two :
    0 < baselPartialExample /\ baselPartialExample < 2 := by
  rw [baselPartialExample_exact]
  native_decide

def baselComparisonExampleMidpoint : Rat := baselCommonInterval.midpoint

theorem baselComparisonExampleMidpoint_in_both :
    (DirichletSeries.zetaTwoInterval 10000).lo <=
        baselComparisonExampleMidpoint /\
      baselComparisonExampleMidpoint <=
        (DirichletSeries.zetaTwoInterval 10000).hi /\
      (geometricPiSquaredOverSixCompute 8).lo <=
        baselComparisonExampleMidpoint /\
      baselComparisonExampleMidpoint <=
        (geometricPiSquaredOverSixCompute 8).hi := by
  simpa [baselComparisonExampleMidpoint] using
    baselCommonInterval_midpoint_certificate

theorem baselComparisonExample_width_le :
    baselCommonInterval.width <=
        (DirichletSeries.zetaTwoInterval 10000).width /\
      baselCommonInterval.width <=
        (geometricPiSquaredOverSixCompute 8).width := by
  exact baselCommonInterval_width_le

end BaselFiniteComparison

end ComputableAnalysis
