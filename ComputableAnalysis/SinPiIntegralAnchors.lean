import ComputableAnalysis.SinPiIntegral

/-!
# Finite regression anchors for the equal-dyadic sine integral

These executable checks are deliberately separate from the reusable sine
integral foundation.  They provide small, finite evidence for the transport
route without making every import of the foundation elaborate the regression
computations.
-/

namespace ComputableAnalysis

namespace SinPiIntegral

theorem dyadicNestedRadicalLeftSum_zero :
    dyadicNestedRadicalLeftSum 0 = { lo := 0, hi := 0 } := by
  native_decide

theorem dyadicNestedRadicalLeftSum_one :
    dyadicNestedRadicalLeftSum 1 =
      { lo := (1 / 4 : Rat) *
          (dyadicNestedRadicalStageSinAt 1 1).lo,
        hi := (1 / 4 : Rat) *
          (dyadicNestedRadicalStageSinAt 1 1).hi } := by
  native_decide

theorem dyadicNestedRadicalLeftSum_one_explicit :
    dyadicNestedRadicalLeftSum 1 =
      { lo := (1 / 4 : Rat) *
          (sqrtOnUnitEvalIntervalClipped
            { lo := (1 : Rat) / 2, hi := (1 : Rat) / 2 } 1).lo,
        hi := (1 / 4 : Rat) *
          (sqrtOnUnitEvalIntervalClipped
            { lo := (1 : Rat) / 2, hi := (1 : Rat) / 2 } 1).hi } := by
  native_decide

theorem dyadicNestedRadicalLeftSum_zero_overlaps_stieltjes :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 0)
      (sinPiStieltjesIntegral.compute 0) := by
  unfold QInterval.Overlaps
  constructor <;> native_decide

theorem dyadicNestedRadicalLeftSum_one_overlaps_stieltjes :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 1)
      (sinPiStieltjesIntegral.compute 1) := by
  unfold QInterval.Overlaps
  constructor <;> native_decide

theorem dyadicNestedRadicalLeftSum_two_overlaps_stieltjes :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 2)
      (sinPiStieltjesIntegral.compute 2) := by
  unfold QInterval.Overlaps
  constructor <;> native_decide

theorem dyadicNestedRadicalLeftSum_three_overlaps_stieltjes :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 3)
      (sinPiStieltjesIntegral.compute 3) := by
  unfold QInterval.Overlaps
  constructor <;> native_decide

theorem dyadicNestedRadicalLeftSum_four_overlaps_stieltjes :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 4)
      (sinPiStieltjesIntegral.compute 4) := by
  unfold QInterval.Overlaps
  constructor <;> native_decide

end SinPiIntegral

end ComputableAnalysis
