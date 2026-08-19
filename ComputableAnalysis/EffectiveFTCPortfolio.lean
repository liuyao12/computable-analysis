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

structure EffectiveFTCPortfolio where
  square_value :
    (Integral.raw
      (FunctionOnInterval.exactRat (fun x : Rat => x * x) 0 1)
      Integral.exactRat_square_integral_certificate).Equiv
      (RealRaw.ofRat (1 / 3))
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

theorem effectiveFTCPortfolio : EffectiveFTCPortfolio where
  square_value := Integral.exactRat_square_integral_raw_equiv_one_third
  cube_value := Integral.exactRat_cube_integral_raw_equiv_one_fourth
  quartic_value := Integral.exactRat_quartic_integral_raw_equiv_one_fifth
  fifth_value := Integral.fifthIntegralEffectiveFTC_equiv_one_sixth
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
