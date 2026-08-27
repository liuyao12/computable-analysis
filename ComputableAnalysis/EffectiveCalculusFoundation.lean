import ComputableAnalysis.IntegralFoundation
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FiniteMonotoneSequenceInterface
import ComputableAnalysis.FinitePolynomialCalculus
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

end ComputableAnalysis.Integral
