import ComputableAnalysis.FiniteFTCIntervalRegular

namespace ComputableAnalysis

namespace Integral

theorem squareIntegralEffectiveFTC_endpoint_equiv_one_third :
    squareIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw.Equiv
      (RealRaw.ofRat (1 / 3)) := by
  have hvalid : RealRaw.ValidCompute
      (endpointDifferenceCompute squareIntegralPrimitiveRaw 0 1) := by
    exact endpointDifference_valid_of_fun_valid
      (F := squareIntegralPrimitiveRaw) (a := 0) (b := 1)
      (RealFunRaw.exact_valid _) trivial trivial
  have hcanon :=
    DerivativeBoundFTC.endpointRaw_equiv_endpointDifference
      squareIntegralEffectiveFTCData.toDerivativeBoundFTC
      (RealFunRaw.exact_valid _) trivial trivial hvalid
  have hendpointValid :
      (endpointDifferenceRaw squareIntegralPrimitiveRaw 0 1 hvalid).Valid := by
    simpa [endpointDifferenceRaw, RealRaw.Valid] using hvalid
  have hrawValid :
      squareIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw.Valid := by
    simp [DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
      DerivativeBoundFTC.endpointInterval, squareIntegralEffectiveFTCData,
      endpointDifferenceInterval, squareIntegralPrimitiveRaw, RealFunRaw.exact,
      RealRaw.ValidCompute, RealRaw.Valid]
    constructor
    · native_decide
    · unfold RealRaw.WidthsShrinkToZero
      intro eps
      refine ⟨0, ?_⟩
      intro n hn
      simp [DerivativeBoundFTC.endpointCompute, DerivativeBoundFTC.endpointInterval,
        endpointDifferenceInterval]
      have hzero :
          ({ lo := 1 ^ 3 / 3 - 0 ^ 3 / 3,
              hi := 1 ^ 3 / 3 - 0 ^ 3 / 3 } : QInterval).width = 0 := by
        native_decide
      rw [hzero]
      exact Rat.le_of_lt eps.property
  have hvalue : (endpointDifferenceRaw squareIntegralPrimitiveRaw 0 1 hvalid).Equiv
      (RealRaw.ofRat (1 / 3)) := by
    apply RealRaw.sameStageOverlap_equiv
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    change QInterval.Overlaps
      (endpointDifferenceInterval squareIntegralPrimitiveRaw 0 1 n)
      { lo := 1 / 3, hi := 1 / 3 }
    unfold endpointDifferenceInterval squareIntegralPrimitiveRaw
      RealFunRaw.exact QInterval.Overlaps
    simp
    native_decide
  exact RealRaw.equiv_trans
    hrawValid hendpointValid (RealRaw.ofRat_valid _) hcanon hvalue

theorem squareIntegralEffectiveFTC_integral_equiv_one_third :
    squareIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (1 / 3)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hFTC := squareIntegralEffectiveFTC_equiv_endpoint n
  have hFTC' := (RealRaw.compareAt_overlap_iff
    squareIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw
    squareIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw n n).1 hFTC
  change QInterval.Overlaps
    (squareIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.compute n)
    { lo := 1 / 3, hi := 1 / 3 }
  have hendpoint :
      squareIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw.compute n =
        { lo := 1 / 3, hi := 1 / 3 } := by
    simp [DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
      DerivativeBoundFTC.endpointInterval, squareIntegralEffectiveFTCData,
      endpointDifferenceInterval, squareIntegralPrimitiveRaw, RealFunRaw.exact]
    native_decide
  rw [hendpoint] at hFTC'
  simpa [DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
    DerivativeBoundFTC.endpointInterval, squareIntegralEffectiveFTCData,
    endpointDifferenceInterval, squareIntegralPrimitiveRaw, RealFunRaw.exact]
    using hFTC'

theorem cubicIntegralEffectiveFTC_integral_equiv_one_fourth :
    cubicIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (1 / 4)) := by
  let H := cubicIntegralEffectiveFTCData.toDerivativeBoundFTC
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hover := H.overlap (precisionAtStage n)
  change QInterval.Overlaps (H.boundedIntegralCompute n)
    { lo := 1 / 4, hi := 1 / 4 }
  have hzero : (1 / 4 : Rat) - 0 / 4 = 1 / 4 := by grind
  simpa [H, DerivativeBoundFTC.boundedIntegralCompute,
    DerivativeBoundFTC.boundedIntegralInterval,
    DerivativeBoundFTC.endpointInterval, endpointDifferenceInterval,
    cubicIntegralPrimitiveRaw, RealFunRaw.exact, Rat.pow_succ, hzero] using hover

end Integral

end ComputableAnalysis
