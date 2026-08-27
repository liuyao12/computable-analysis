import ComputableAnalysis.CircleFoundation
import ComputableAnalysis.Calculus
import ComputableAnalysis.IdentityInverse
import ComputableAnalysis.ArctanEffectiveFTC
import ComputableAnalysis.ArctanScheduledCore
import ComputableAnalysis.IntegralIdentities
import ComputableAnalysis.TurningPointIntegral
import ComputableAnalysis.AbsIntegral
import ComputableAnalysis.PrimitivePiecewiseFTC
import ComputableAnalysis.FiniteFTCIntervalRegular
import ComputableAnalysis.FiniteSinePrefixFTC
import ComputableAnalysis.PolynomialFTCValues
import ComputableAnalysis.FiniteFTCPolynomial
import ComputableAnalysis.SinPiIntegral
import ComputableAnalysis.SinPiTransportSubgoals
import ComputableAnalysis.SinPiTransportAdapter
import ComputableAnalysis.SinPiSquareFTC
import ComputableAnalysis.TangentPullbackEffectiveFTC
import ComputableAnalysis.StableRotationDerivative
import ComputableAnalysis.EffectiveFTCPortfolio
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

end ComputableAnalysis.Integral
