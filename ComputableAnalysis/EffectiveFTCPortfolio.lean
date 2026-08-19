import ComputableAnalysis.ArctanEffectiveFTC
import ComputableAnalysis.ExpProofs
import ComputableAnalysis.FiniteSinePrefixFTC
import ComputableAnalysis.FiniteFTCIntervalRegular
import ComputableAnalysis.FiniteFTCQuartic
import ComputableAnalysis.SinPiSquareFTC
import ComputableAnalysis.TangentPullbackEffectiveFTC

/-!
# Auditable effective-FTC portfolio

This module records the concrete certificates that currently form the
effective-FTC ladder.  It is intentionally a bundle of theorem statements,
not a claim that every continuous function is integrable: each field is backed
by a finite rational interval certificate in the imported module.

The nested-radical `sin^2` transport is not included in the completed bundle;
its unfinished endpoint bridge is tracked in `SinPiSquareFTC.lean`.
-/

namespace ComputableAnalysis

theorem squareEffectiveFTC_endpointRaw_valid :
    (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw).Valid := by
  have heq :
      (fun n => endpointDifferenceCompute Integral.squarePrimitiveRaw 0 1
        (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.chooseEndpointPrecision
          (precisionAtStage n))) =
      (fun _ => ({ lo := 1, hi := 1 } : QInterval)) := by
    funext n
    simp [Integral.squareEffectiveFTCData,
      DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
      Integral.squarePrimitiveRaw, RealFunRaw.exact,
      endpointDifferenceCompute, endpointDifferenceInterval]
    native_decide

  change RealRaw.ValidCompute
    (fun n => endpointDifferenceCompute Integral.squarePrimitiveRaw 0 1
      (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.chooseEndpointPrecision
        (precisionAtStage n)))
  rw [heq]
  unfold RealRaw.ValidCompute
  constructor
  · intro n
    simp [QInterval.width] <;> grind
  constructor
  · intro n m hnm
    simp
  · intro eps
    refine ⟨0, ?_⟩
    intro n hn
    simp [QInterval.width] <;> grind

theorem cubeEffectiveFTC_endpointRaw_valid :
    (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.endpointRaw).Valid := by
  have heq :
      (fun n => endpointDifferenceCompute Integral.cubePrimitiveRaw 0 1
        (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.chooseEndpointPrecision
          (precisionAtStage n))) =
      (fun _ => ({ lo := 1, hi := 1 } : QInterval)) := by
    funext n
    simp [Integral.cubeEffectiveFTCData,
      DerivativeBoundFTC.endpointRaw, DerivativeBoundFTC.endpointCompute,
      Integral.cubePrimitiveRaw, RealFunRaw.exact,
      endpointDifferenceCompute, endpointDifferenceInterval]
    native_decide
  change RealRaw.ValidCompute
    (fun n => endpointDifferenceCompute Integral.cubePrimitiveRaw 0 1
      (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.chooseEndpointPrecision
        (precisionAtStage n)))
  rw [heq]
  unfold RealRaw.ValidCompute
  constructor
  · intro n
    simp [QInterval.width] <;> grind
  constructor
  · intro n m hnm
    simp
  · intro eps
    refine ⟨0, ?_⟩
    intro n hn
    simp [QInterval.width] <;> grind

structure EffectiveFTCPortfolio where
  square_value :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      Integral.exactRat_square_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 3))
  square_effective_value :
    Integral.squareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat 1)
  cube_effective_value :
    Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat 1)
  quartic_effective_value :
    Integral.quarticIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (1 / 5))
  sine_prefix_square_value :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (6389 / 161280))
  tangent_pullback_value :
    SinPiIntegral.tangentPullbackIntegral.Equiv (RealRaw.ofRat 1)
  cube_value :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 3) 0 1)
      Integral.exactRat_cube_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 4))
  quartic_value :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x ^ 4) 0 1)
      Integral.exactRat_quartic_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 5))
  fifth_value :
    Integral.fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (1 / 6))
  square :
    (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.squareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  cube :
    (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  quartic :
    (Integral.quarticEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.quarticEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  fifth :
    (Integral.fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  arctan :
    (Integral.arctanEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw).Equiv
      Integral.arctanEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  tangentPullback :
    SinPiIntegral.tangentPullbackCandidateFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      SinPiIntegral.tangentPullbackCandidateFTCData.toDerivativeBoundFTC.endpointRaw
  sinePrefixSquare :
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw
  exponential :
    (ExpProofs.uniformExpOnUnit_selectedStageFTCIndexed.toSelected.boundedIntegralRaw).Equiv
      ExpProofs.uniformExpOnUnit_selectedStageFTCIndexed.toSelected.endpointRaw

structure TangentSquareIntegralValueSubgoal where
  lower_contains :
    forall n, (SinPiIntegral.tangentSquareIntegral.compute n).lo <= (1 / 4 : Rat)
  upper_contains :
    forall n, (1 / 4 : Rat) <= (SinPiIntegral.tangentSquareIntegral.compute n).hi

theorem tangentSquareIntegral_stage_zero_contains_quarter :
    QInterval.Overlaps
      (SinPiIntegral.tangentSquareIntegral.compute 0)
      ({ lo := (1 / 4 : Rat), hi := 1 / 4 } : QInterval) := by
  unfold QInterval.Overlaps
  rw [SinPiIntegral.tangentSquareIntegral_compute]
  native_decide

theorem tangentSquareLeftSum_stage_one_quarter_certificate :
    ((1 / 4 : Rat) - (64 : Rat) / (((2 ^ 1 : Nat) : Rat)) <=
        IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ 1)) ∧
      (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ 1) <=
        (1 / 4 : Rat) + (64 : Rat) / (((2 ^ 1 : Nat) : Rat))) := by
  native_decide

theorem tangentSquareLeftSum_stage_two_quarter_certificate :
    ((1 / 4 : Rat) - (64 : Rat) / (((2 ^ 2 : Nat) : Rat)) <=
        IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ 2)) ∧
      (IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ 2) <=
        (1 / 4 : Rat) + (64 : Rat) / (((2 ^ 2 : Nat) : Rat))) := by
  native_decide

structure TangentSquareLeftSumQuarterCertificate where
  lower_sum :
    forall n,
      IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
          SinPiIntegral.tangentSquareDensity (2 ^ n) <=
        (1 / 4 : Rat) +
          (64 : Rat) / (((2 ^ n : Nat) : Rat))
  upper_sum :
    forall n,
      (1 / 4 : Rat) -
          (64 : Rat) / (((2 ^ n : Nat) : Rat))
          <= IntegralIdentities.LipschitzDyadic.uniformLeftEndpointSum
            SinPiIntegral.tangentSquareDensity (2 ^ n)

theorem TangentSquareLeftSumQuarterCertificate.to_value_subgoal
    (H : TangentSquareLeftSumQuarterCertificate) :
    TangentSquareIntegralValueSubgoal := by
  constructor
  · intro n
    have hmargin :=
      IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum_margin
        SinPiIntegral.tangentSquareDensity_lipschitz_on_unit n
    rw [SinPiIntegral.tangentSquareIntegral_compute]
    change (IntegralIdentities.LipschitzDyadic.compute
      SinPiIntegral.tangentSquareDensity 64 n).lo <= (1 / 4 : Rat)
    have hleft := hmargin.1
    have hsum := H.lower_sum n
    exact Rat.le_trans hleft (by
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm])
  · intro n
    have hmargin :=
      IntegralIdentities.LipschitzDyadic.compute_contains_uniformLeftEndpointSum_margin
        SinPiIntegral.tangentSquareDensity_lipschitz_on_unit n
    rw [SinPiIntegral.tangentSquareIntegral_compute]
    change (1 / 4 : Rat) <=
      (IntegralIdentities.LipschitzDyadic.compute
        SinPiIntegral.tangentSquareDensity 64 n).hi
    have hright := hmargin.2
    have hsum := H.upper_sum n
    exact Rat.le_trans (by
      grind [Rat.sub_eq_add_neg, Rat.div_def, Rat.mul_assoc, Rat.mul_comm]) hright

structure TangentSquareFTCIntegralCompatibilitySubgoal where
  stage_overlap :
    forall n, QInterval.Overlaps
      (SinPiIntegral.tangentSquareEffectiveIntegralRaw.compute n)
      (SinPiIntegral.tangentSquareIntegral.compute n)

structure TangentSquareFTCIntegralCommonWitness where
  witness : Nat -> Rat
  effective_lo_le :
    forall n,
      (SinPiIntegral.tangentSquareEffectiveIntegralRaw.compute n).lo <= witness n
  witness_le_effective_hi :
    forall n,
      witness n <= (SinPiIntegral.tangentSquareEffectiveIntegralRaw.compute n).hi
  anchor_lo_le :
    forall n,
      (SinPiIntegral.tangentSquareIntegral.compute n).lo <= witness n
  witness_le_anchor_hi :
    forall n,
      witness n <= (SinPiIntegral.tangentSquareIntegral.compute n).hi

theorem TangentSquareFTCIntegralCommonWitness.to_compatibility
    (H : TangentSquareFTCIntegralCommonWitness) :
    TangentSquareFTCIntegralCompatibilitySubgoal := by
  exact {
    stage_overlap := fun n => by
      unfold QInterval.Overlaps
      exact ⟨Rat.le_trans (H.effective_lo_le n)
          (H.witness_le_anchor_hi n),
        Rat.le_trans (H.anchor_lo_le n)
          (H.witness_le_effective_hi n)⟩ }

theorem TangentSquareFTCIntegralCompatibilitySubgoal.equivalent
    (H : TangentSquareFTCIntegralCompatibilitySubgoal) :
    SinPiIntegral.tangentSquareEffectiveIntegralRaw.Equiv
      SinPiIntegral.tangentSquareIntegral := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  exact (RealRaw.compareAt_overlap_iff
    SinPiIntegral.tangentSquareEffectiveIntegralRaw
    SinPiIntegral.tangentSquareIntegral n n).2 (H.stage_overlap n)

theorem TangentSquareIntegralValueSubgoal.value
    (H : TangentSquareIntegralValueSubgoal) :
    SinPiIntegral.tangentSquareIntegral.Equiv (RealRaw.ofRat (1 / 4)) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    SinPiIntegral.tangentSquareIntegral (RealRaw.ofRat (1 / 4)) n n).2
  change QInterval.Overlaps
    (SinPiIntegral.tangentSquareIntegral.compute n)
    ((RealRaw.ofRat (1 / 4)).compute n)
  unfold QInterval.Overlaps RealRaw.ofRat
  exact ⟨H.lower_contains n, H.upper_contains n⟩

/-! The remaining genuine `sin(pi*x)^2` transport is packaged as two finite
certificates.  The closure theorem below is unconditional once these fields
are supplied; no completed-real existence theorem is hidden in the package. -/
structure NestedRadicalSinPiSquareValueSubgoal where
  commonWitness :
    SinPiIntegral.DyadicNestedRadicalSquareTangentCommonWitness
  tangentAnchorValue :
    TangentSquareIntegralValueSubgoal

theorem NestedRadicalSinPiSquareValueSubgoal.value
    (H : NestedRadicalSinPiSquareValueSubgoal) :
    (SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized
      SinPiIntegral.tangentSquareIntegral).Equiv
      (RealRaw.ofRat (1 / 4)) := by
  exact SinPiIntegral.dyadicNestedRadicalSquareIntegralRaw_stabilized_equiv_value_of_anchor
    H.commonWitness.to_equiv H.tangentAnchorValue.value

theorem effectiveFTCPortfolio : EffectiveFTCPortfolio where
  square_value := Integral.exactRat_square_integral_raw_equiv_one_third
  cube_value := Integral.exactRat_cube_integral_raw_equiv_one_fourth
  quartic_value := Integral.exactRat_quartic_integral_raw_equiv_one_fifth
  fifth_value := Integral.fifthIntegralEffectiveFTC_equiv_one_sixth
  square_effective_value := by
    intro n
    apply (RealRaw.compareAt_overlap_iff
      Integral.squareEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw
      (RealRaw.ofRat 1) n n).2
    let H := Integral.squareEffectiveFTCData.toDerivativeBoundFTC
    change QInterval.Overlaps
      (H.boundedIntegralInterval (precisionAtStage n))
      ({ lo := 1, hi := 1 } : QInterval)
    have hover := H.overlap (precisionAtStage n)
    simp [H, Integral.squareEffectiveFTCData, endpointDifferenceInterval,
      Integral.squarePrimitiveRaw, RealFunRaw.exact] at hover
    simp [H, DerivativeBoundFTC.boundedIntegralInterval,
      DerivativeBoundFTC.endpointInterval,
      Integral.squareEffectiveFTCData, Integral.squarePrimitiveRaw,
      RealFunRaw.exact, endpointDifferenceInterval] at ⊢
    unfold QInterval.Overlaps at hover ⊢
    grind
  cube_effective_value := by
    intro n
    apply (RealRaw.compareAt_overlap_iff
      Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw
      (RealRaw.ofRat 1) n n).2
    let H := Integral.cubeEffectiveFTCData.toDerivativeBoundFTC
    change QInterval.Overlaps
      (H.boundedIntegralInterval (precisionAtStage n))
      ({ lo := 1, hi := 1 } : QInterval)
    have hover := H.overlap (precisionAtStage n)
    simp [H, Integral.cubeEffectiveFTCData, endpointDifferenceInterval,
      Integral.cubePrimitiveRaw, RealFunRaw.exact] at hover
    simp [H, DerivativeBoundFTC.boundedIntegralInterval,
      Integral.cubeEffectiveFTCData, Integral.cubePrimitiveRaw,
      RealFunRaw.exact] at ⊢
    unfold QInterval.Overlaps at hover ⊢
    grind
  quartic_effective_value := Integral.quarticIntegralEffectiveFTC_equiv_one_fifth
  sine_prefix_square_value :=
    FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_value
  tangent_pullback_value := SinPiIntegral.tangentPullbackIntegral_equiv_one
  square := Integral.squareEffectiveFTC_equiv_endpoint
  cube := Integral.cubeEffectiveFTC_equiv_endpoint
  quartic := Integral.quarticEffectiveFTC_equiv_endpoint
  fifth := Integral.fifthIntegralEffectiveFTC_equiv_endpoint
  arctan := Integral.arctanEffectiveFTC_equiv_endpoint
  tangentPullback := SinPiIntegral.tangentPullbackEffectiveFTC_equiv_endpoint
  sinePrefixSquare := FiniteSinePrefix.sineTaylorPrefixThreeSquareEffectiveFTC_equiv_endpoint
  exponential := ExpProofs.uniformExpOnUnit_effectiveFTC

/-!
The next rung is deliberately represented by the exact missing proof data.
The generic certificate already turns the integral into an endpoint raw; the
only remaining value theorem is that this endpoint raw is `1/4`.
-/

structure SinPiSquareEffectiveFTCEndpointSubgoal
    (S : SinPiIntegral.ArctanSinPiConstruction) where
  data : SinPiIntegral.SinPiSquareEffectiveFTCData S
  endpoint_value :
    data.endpointRaw.Equiv (RealRaw.ofRat (1 / 4))

theorem SinPiSquareEffectiveFTCEndpointSubgoal.integral_value
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (H : SinPiSquareEffectiveFTCEndpointSubgoal S) :
    H.data.integralRaw.Equiv (RealRaw.ofRat (1 / 4)) := by
  exact H.data.endpoint_equiv_of_value H.endpoint_value

end ComputableAnalysis
