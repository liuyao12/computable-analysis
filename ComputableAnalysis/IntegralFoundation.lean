import ComputableAnalysis.RationalCircle
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
