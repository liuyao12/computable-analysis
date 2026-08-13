import ComputableAnalysis.BaselFiniteComparison

/-!
# A million-term finite Basel cross-check

This is a tighter finite comparison between the reciprocal-square interval and
the geometric `pi^2 / 6` interval.  It is evidence for the target interface,
not Euler's completed Basel identity.
-/

namespace ComputableAnalysis

namespace BaselFiniteComparison

def baselMillionCommonInterval : QInterval :=
  QInterval.intersection
    (DirichletSeries.zetaTwoInterval 1000000)
    (geometricPiSquaredOverSixCompute 16)

theorem zetaTwoInterval_overlaps_projectPiSquaredOverSix_1000000_16 :
    (DirichletSeries.zetaTwoInterval 1000000).lo <=
        (geometricPiSquaredOverSixCompute 16).hi /\
      (geometricPiSquaredOverSixCompute 16).lo <=
        (DirichletSeries.zetaTwoInterval 1000000).hi := by
  native_decide

theorem baselMillionCommonInterval_certificate :
    baselMillionCommonInterval.lo <= baselMillionCommonInterval.hi /\
      (DirichletSeries.zetaTwoInterval 1000000).ContainsInterval
        baselMillionCommonInterval /\
      (geometricPiSquaredOverSixCompute 16).ContainsInterval
        baselMillionCommonInterval := by
  refine ⟨?_, ?_, ?_⟩
  · exact QInterval.intersection_ordered_of_overlaps
      (DirichletSeries.zetaTwoInterval_ordered 1000000)
      (by native_decide)
      zetaTwoInterval_overlaps_projectPiSquaredOverSix_1000000_16
  · exact QInterval.intersection_contained_left _ _
  · exact QInterval.intersection_contained_right _ _

theorem baselMillionCommonInterval_width_le :
    baselMillionCommonInterval.width <=
        (DirichletSeries.zetaTwoInterval 1000000).width /\
      baselMillionCommonInterval.width <=
        (geometricPiSquaredOverSixCompute 16).width := by
  constructor
  · exact QInterval.width_le_of_contains
      (QInterval.intersection_contained_left _ _)
  · exact QInterval.width_le_of_contains
      (QInterval.intersection_contained_right _ _)

theorem baselMillionCommonInterval_midpoint_certificate :
    let q := baselMillionCommonInterval.midpoint
    (DirichletSeries.zetaTwoInterval 1000000).lo <= q /\
      q <= (DirichletSeries.zetaTwoInterval 1000000).hi /\
      (geometricPiSquaredOverSixCompute 16).lo <= q /\
      q <= (geometricPiSquaredOverSixCompute 16).hi := by
  let q := baselMillionCommonInterval.midpoint
  have hordered : baselMillionCommonInterval.lo <=
      baselMillionCommonInterval.hi := by
    exact (baselMillionCommonInterval_certificate).1
  have hmid := QInterval.midpoint_mem hordered
  have hzeta := (baselMillionCommonInterval_certificate).2.1
  have hpi := (baselMillionCommonInterval_certificate).2.2
  dsimp [q]
  exact ⟨Rat.le_trans hzeta.1 hmid.1,
    Rat.le_trans hmid.2 hzeta.2,
    Rat.le_trans hpi.1 hmid.1,
    Rat.le_trans hmid.2 hpi.2⟩

end BaselFiniteComparison

end ComputableAnalysis
