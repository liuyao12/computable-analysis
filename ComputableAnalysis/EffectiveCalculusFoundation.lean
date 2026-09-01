import ComputableAnalysis.IntegralFoundation
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FiniteMonotoneSequenceInterface
import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.FiniteLHopitalCertificate
import ComputableAnalysis.FiniteGapAwareInverseSearch

/-!
# Effective calculus foundation

This scoped entry point collects the finite secant, derivative-bound,
curvature, stabilization, inverse-search, and L'Hôpital contracts that turn
an explicit interval evaluator into an effective FTC certificate.

It is a proof interface, not a general completeness theorem: each special
function supplies its own domain, schedule, and finite overlap data.  Routine
scalar, signed, and piecewise variants are transported or assembled from the
representative certificates.
-/

namespace ComputableAnalysis.Integral

/-- The curvature certificate's bounded integral is the normalized square
integral, whose finite endpoint value is one. -/
theorem effectiveSquareCurvatureFTC_value_one :
    squareCurvatureFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat 1) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff
    squareCurvatureFTCData.toDerivativeBoundFTC.boundedIntegralRaw
    (RealRaw.ofRat 1) n n).2
  let H := squareCurvatureFTCData.toDerivativeBoundFTC
  change QInterval.Overlaps
    (H.boundedIntegralInterval (precisionAtStage n))
    ({ lo := 1, hi := 1 } : QInterval)
  have hover := H.overlap (precisionAtStage n)
  simp [H, squareCurvatureFTCData, squareEffectiveFTCData,
    endpointDifferenceInterval, squarePrimitiveRaw, RealFunRaw.exact] at hover
  simp [H, DerivativeBoundFTC.boundedIntegralInterval,
    squareCurvatureFTCData, squareEffectiveFTCData, squarePrimitiveRaw,
    RealFunRaw.exact] at ⊢
  unfold QInterval.Overlaps at hover ⊢
  grind


end ComputableAnalysis.Integral
