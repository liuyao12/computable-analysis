import ComputableAnalysis.IntegralFoundation
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FiniteMonotoneSequenceInterface
import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.PolynomialMeanValue
import ComputableAnalysis.FiniteLHopitalCertificate
import ComputableAnalysis.FiniteGapAwareInverseSearch
import ComputableAnalysis.EffectiveFTCPortfolio

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

/-! Curvature is the intended provider-facing route to the effective FTC:
convex and concave functions supply monotone derivative bounds, while this
wrapper closes the same finite endpoint certificate. -/
theorem effectiveCurvatureFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact curvatureFTC h

/-- Convex providers can close the effective FTC directly. -/
theorem effectiveConvexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact convexFTC h

/-- Concave providers can close the effective FTC directly. -/
theorem effectiveConcaveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact concaveFTC h

/-- The square function is the first complete concrete curvature client: its
finite convexity bounds feed the effective FTC and close at the endpoint
difference. -/
theorem effectiveSquareCurvatureFTC :
    squareCurvatureFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      squareCurvatureFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact squareCurvatureFTC_equiv_endpoint

/-- The curvature certificate's bounded integral is the normalized square
integral, whose finite endpoint value is one. -/
theorem effectiveSquareCurvatureFTC_value_one :
    squareCurvatureFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat 1) := by
  exact effectiveFTCPortfolio.square_effective_value

/-! The scoped entry point gives the finite-piece FTC its project-facing name.
The partition, cell endpoint certificates, and endpoint transport remain
explicit inputs; this wrapper adds no completeness or general continuity
assumption. -/
theorem effectiveGeneralIntegralFor_equiv_totalEndpointDifference_of_telescope
    (F : FunctionOnInterval)
    (c : GeneralConstructionFor F)
    (h : PiecewiseMonotoneEndpointFTCFor F c)
    {first : RealRaw} {rest : List RealRaw}
    (hvalues : forall x, x ∈ first :: rest -> x.Valid)
    (htransport :
      FiniteRawListEquiv
        (piecewiseMonotoneEndpointDifferenceList F c)
        (rawAdjacentDifferenceList (first :: rest)))
    (htotal : (rawLast first rest - first).Equiv
      (piecewiseMonotoneTotalEndpointDifference F c)) :
    (generalIntegralFor F c).Equiv
      (piecewiseMonotoneTotalEndpointDifference F c) := by
  exact generalIntegralFor_equiv_totalEndpointDifference_of_telescope
    F c h hvalues htransport htotal

/-! Publicly expose the finite mean-value conclusion through the effective
calculus entry point.  The conclusion is an overlap of rational boxes, so it
does not select an attained intermediate real number. -/
theorem effectiveMeanValueBracket
    {F dF : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C)
    (hF : F.Valid) (hwidth : 0 < C.width) (n : Nat) :
    QInterval.Overlaps
      (H.bound n)
      (QInterval.divByRat
        (endpointDifferenceInterval F C.lower C.upper
          (H.endpointPrecision n))
        C.width) := by
  exact CandidateDerivativeCellControl.endpoint_average_overlaps_bound
    H hF hwidth n

end ComputableAnalysis.Integral

namespace ComputableAnalysis

/-! Composition closure for effective derivatives.  The caller supplies the
inner positivity, radius transports, and weighted error budget; all remaining
work is finite rational error arithmetic. -/
def effectiveDerivativeCompositionOfBudget
    {f df g dg : Rat -> Rat}
    (outer : EffectiveDerivativeExact f df)
    (inner : EffectiveDerivativeExact g dg)
    (outerTol innerTol : QPos -> QPos)
    (stepRadius : QPos -> QPos)
    (hinner_pos : forall (eps : QPos) (x h : Rat),
      0 < h -> h <= (stepRadius eps).val ->
        0 < g (x + h) - g x)
    (hinner_radius : forall (eps : QPos) (x h : Rat),
      0 < h -> h <= (stepRadius eps).val ->
        h <= (inner.stepRadius (innerTol eps)).val)
    (houter_radius : forall (eps : QPos) (x h : Rat),
      0 < h -> h <= (stepRadius eps).val ->
        g (x + h) - g x <=
          (outer.stepRadius (outerTol eps)).val)
    (hbudget : forall (eps : QPos) (x h : Rat),
      0 < h -> h <= (stepRadius eps).val ->
      qabs (ExactFunction.differenceQuotient f (g x)
        (g (x + h) - g x)) *
          (innerTol eps).val +
        qabs (dg x) * (outerTol eps).val <= eps.val) :
    EffectiveDerivativeExact (fun x => f (g x))
      (fun x => df (g x) * dg x) :=
  ExactFunction.EffectiveDerivativeExact.compOfBudget
    outer inner outerTol innerTol stepRadius hinner_pos hinner_radius
    houter_radius hbudget

end ComputableAnalysis
