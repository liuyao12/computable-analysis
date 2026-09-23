import ComputableAnalysis.Basel.EulerProduct

namespace ComputableAnalysis.Basel

/-- Basel transports irrationality of the square of geometric pi to the
reciprocal-square series. Irrationality of pi alone is not sufficient. -/
theorem zetaTwo_irrational_of_basel_of_piSquare_irrational
    (hbasel : eulerBasel_geometricPi) (hpi : (piCircleArea*piCircleArea).Irrational) :
    DirichletSeries.zetaTwoRaw.Irrational := by
  intro q hq
  have hr : geometricPiSquaredOverSixRaw.Equiv (RealRaw.ofRat q) :=
    RealRaw.equiv_trans geometricPiSquaredOverSixRaw_valid baselSeriesRaw_valid
      (RealRaw.ofRat_valid q) (RealRaw.equiv_symm hbasel) hq
  apply hpi (6*q)
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have h := (RealRaw.compareAt_overlap_iff _ _ n n).mp (hr n)
  dsimp only [geometricPiSquaredOverSixRaw, piSquaredOverSixRaw,
    RealRaw.scaleRat, RealRaw.scaleRatCompute] at h
  rw [if_pos (by grind only [Rat.div_def])] at h
  change (1/6)*((piCircleArea*piCircleArea).compute n).lo≤q ∧
    q≤(1/6)*((piCircleArea*piCircleArea).compute n).hi at h
  change ((piCircleArea*piCircleArea).compute n).lo≤6*q ∧
    6*q≤((piCircleArea*piCircleArea).compute n).hi
  grind only [Rat.div_def]

end ComputableAnalysis.Basel
