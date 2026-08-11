import ComputableAnalysis.BaselFiniteComparison

/-!
# A supplied-target Basel containment certificate

This module strengthens finite overlap to containment of a later zeta(2)
interval inside a supplied geometric pi^2 / 6 target interval.  It remains
a comparison of finite rational algorithms, not Euler's Basel identity.
-/

namespace ComputableAnalysis

namespace BaselFiniteComparison

theorem zetaTwoInterval_100000_contained_in_expanded_geometricPiSquaredOverSix_10 :
    (QInterval.expand (geometricPiSquaredOverSixCompute 10)
      (DirichletSeries.zetaTwoInterval 100000).width).ContainsInterval
      (DirichletSeries.zetaTwoInterval 100000) := by
  apply QInterval.expand_contains_right_of_overlaps
  · unfold QInterval.Overlaps
    have h := zetaTwoInterval_overlaps_projectPiSquaredOverSix_100000_10
    exact ⟨h.2, h.1⟩
  · exact Rat.le_refl

theorem zetaTwoInterval_100000_target_certificate :
    (QInterval.expand (geometricPiSquaredOverSixCompute 10)
      (DirichletSeries.zetaTwoInterval 100000).width).lo <=
        (DirichletSeries.zetaTwoInterval 100000).lo /\
      (DirichletSeries.zetaTwoInterval 100000).hi <=
        (QInterval.expand (geometricPiSquaredOverSixCompute 10)
          (DirichletSeries.zetaTwoInterval 100000).width).hi := by
  exact zetaTwoInterval_100000_contained_in_expanded_geometricPiSquaredOverSix_10

end BaselFiniteComparison

end ComputableAnalysis
