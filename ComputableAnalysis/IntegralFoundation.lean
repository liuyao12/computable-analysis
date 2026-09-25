import ComputableAnalysis.IntegralEnclosureExamples
import ComputableAnalysis.CircleFoundation
import ComputableAnalysis.Calculus
import ComputableAnalysis.IdentityInverse
import ComputableAnalysis.ArctanEffectiveFTC
import ComputableAnalysis.IntegralIdentities
import ComputableAnalysis.TurningPointIntegral
import ComputableAnalysis.AbsIntegral
import ComputableAnalysis.PrimitivePiecewiseFTC
import ComputableAnalysis.FiniteFTCIntervalRegular
import ComputableAnalysis.FinitePiecewiseRectangles
import ComputableAnalysis.FiniteSinePrefixFTC
import ComputableAnalysis.PolynomialFTCValues
import ComputableAnalysis.SinPiIntegral
import ComputableAnalysis.TangentPullbackEffectiveFTC
import ComputableAnalysis.StableRotationDerivative
import ComputableAnalysis.FiniteLHopitalCertificate
import ComputableAnalysis.MonotonicityConvexity

/-!
# Computable integral and effective-FTC foundation

This scoped entry point collects the finite rectangle, piecewise, polynomial,
arctangent, Stieltjes, and effective-FTC interfaces.  It exposes one
representative computation for each integration pattern; routine scalar or
piecewise variants are obtained by transport and finite assembly.

The imports expose rational interval computations and proof certificates.  No
completed real-number or measurable-function foundation is introduced here.
-/

namespace ComputableAnalysis.Integral

/-! The decreasing Darboux schedule has the same arbitrary-precision public
contract as the increasing schedule.  The witness comes from its explicit
width-shrink certificate, not from completeness of an ambient real space. -/
theorem nonincreasingDarbouxSchedule_precision_witness
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NonincreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (schedule : NonincreasingDarbouxSchedule F hregular hmonotone hinterval)
    (eps : QPos) :
    ∃ n : Nat,
      ((nonincreasingDarbouxScheduleIntegralFor schedule).compute n).width
        <= eps.val := by
  obtain ⟨n, hn⟩ :=
    (nonincreasingDarbouxScheduleRaw_valid schedule).2.2 eps
  exact ⟨n, hn n (Nat.le_refl n)⟩

/-! The matching increasing-side witness is exported here as well.  Both
orientations therefore satisfy the same user-facing precision contract. -/
theorem monotoneDarbouxSchedule_precision_witness
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (schedule : MonotoneDarbouxSchedule F hregular hmonotone hinterval)
    (eps : QPos) :
    ∃ n : Nat,
      ((monotoneDarbouxScheduleIntegralFor schedule).compute n).width
        <= eps.val := by
  obtain ⟨n, hn⟩ :=
    (monotoneDarbouxScheduleRaw_valid schedule).2.2 eps
  exact ⟨n, hn n (Nat.le_refl n)⟩

/-! Public FTC additivity: once three finite constructions have endpoint
identities, additivity over adjacent intervals is only the rational endpoint
telescope.  No completeness or completed real-valued integral is involved. -/
theorem effectiveIntegral_add_of_endpoint_additive
    {integrandAB primitiveAB integrandBC primitiveBC integrandAC primitiveAC :
      FunctionOnInterval}
    (Iab : EndpointComparisonFor integrandAB primitiveAB)
    (Ibc : EndpointComparisonFor integrandBC primitiveBC)
    (Iac : EndpointComparisonFor integrandAC primitiveAC)
    (hendpoint :
      ((endpointDifferenceRaw primitiveAB.toRealFunRaw
          integrandAB.lower integrandAB.upper Iab.endpoint_valid) +
        (endpointDifferenceRaw primitiveBC.toRealFunRaw
          integrandBC.lower integrandBC.upper Ibc.endpoint_valid)).Equiv
          (endpointDifferenceRaw primitiveAC.toRealFunRaw
            integrandAC.lower integrandAC.upper Iac.endpoint_valid)) :
    ((Integral.candidateValue integrandAB Iab.construction) +
      (Integral.candidateValue integrandBC Ibc.construction)).Equiv
        (Integral.candidateValue integrandAC Iac.construction) := by
  exact EndpointComparisonFor.integral_add_equiv_of_endpoint_additive
    Iab Ibc Iac hendpoint

/-! Rational scaling is transported in exactly the same way: the scaled
integral and the scaled primitive endpoint difference are related by the
finite certificate, while `RealRaw.scaleRat` performs the representation
change. -/
theorem effectiveIntegral_scaleRat_of_endpoint_scaleRat
    {integrand primitive scaledIntegrand scaledPrimitive : FunctionOnInterval}
    {r : Rat}
    (I : EndpointComparisonFor integrand primitive)
    (J : EndpointComparisonFor scaledIntegrand scaledPrimitive)
    (hendpoint :
      (endpointDifferenceRaw scaledPrimitive.toRealFunRaw
        scaledIntegrand.lower scaledIntegrand.upper J.endpoint_valid).Equiv
        (RealRaw.scaleRat r
          (endpointDifferenceRaw primitive.toRealFunRaw
            integrand.lower integrand.upper I.endpoint_valid))) :
    (Integral.candidateValue scaledIntegrand J.construction).Equiv
      (RealRaw.scaleRat r
        (Integral.candidateValue integrand I.construction)) := by
  exact EndpointComparisonFor.integral_scaleRat_equiv_of_endpoint_scaleRat
    I J hendpoint

/-! Order is likewise an endpoint fact once the two FTC identities are known.
The result is an order relation between raw interval algorithms, not an
appeal to an order-complete real field. -/
theorem effectiveIntegral_le_of_endpoint_le
    {integrandF primitiveF integrandG primitiveG : FunctionOnInterval}
    (IF : EndpointComparisonFor integrandF primitiveF)
    (IG : EndpointComparisonFor integrandG primitiveG)
    (hendpoint :
      (endpointDifferenceRaw primitiveF.toRealFunRaw
        integrandF.lower integrandF.upper IF.endpoint_valid).Le
        (endpointDifferenceRaw primitiveG.toRealFunRaw
          integrandG.lower integrandG.upper IG.endpoint_valid)) :
    (Integral.candidateValue integrandF IF.construction).Le
      (Integral.candidateValue integrandG IG.construction) := by
  exact EndpointComparisonFor.integral_le_of_endpoint_le IF IG hendpoint

end ComputableAnalysis.Integral
