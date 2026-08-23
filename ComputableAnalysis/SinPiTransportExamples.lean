import ComputableAnalysis.SinPiIntegral

namespace ComputableAnalysis

namespace SinPiIntegral

/-! Small finite checkpoints for the nested-radical sine transport.  They are
kept separate from the certificate adapters because their `native_decide`
proofs intentionally evaluate concrete stages. -/

theorem dyadicNestedRadicalStieltjes_base_witness :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 0)
      (sinPiStieltjesIntegral.compute 0) := by
  unfold QInterval.Overlaps
  constructor
  · rw [dyadicNestedRadicalLeftSum_zero]
    change 0 <= (sinPiStieltjesIntegral.compute 0).hi
    native_decide
  · rw [dyadicNestedRadicalLeftSum_zero]
    change (sinPiStieltjesIntegral.compute 0).lo <= 0
    native_decide

theorem dyadicNestedRadicalStieltjes_stage_one_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 1)
      (sinPiStieltjesIntegral.compute 1) := by
  unfold QInterval.Overlaps
  native_decide

theorem dyadicNestedRadicalStieltjes_stage_two_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 2)
      (sinPiStieltjesIntegral.compute 2) := by
  unfold QInterval.Overlaps
  native_decide

theorem dyadicNestedRadicalStieltjes_stage_three_overlap :
    QInterval.Overlaps
      (dyadicNestedRadicalLeftSum 3)
      (sinPiStieltjesIntegral.compute 3) := by
  unfold QInterval.Overlaps
  native_decide

end SinPiIntegral

end ComputableAnalysis
