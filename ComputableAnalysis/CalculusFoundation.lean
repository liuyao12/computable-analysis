import ComputableAnalysis.IntegralFoundation
import ComputableAnalysis.EffectiveCalculusFoundation
import ComputableAnalysis.PowerSeries
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FiniteSineIntegral
import ComputableAnalysis.FiniteMonotoneSequenceInterface
import ComputableAnalysis.Series
import ComputableAnalysis.FirstYearCalculus
import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.FiniteFourierOrthogonality
import ComputableAnalysis.EffectiveFourierSeries
import ComputableAnalysis.EffectiveFourierTail
import ComputableAnalysis.ExponentialLogarithmFoundation
import ComputableAnalysis.ScalarODEUniqueness
import ComputableAnalysis.PeanoBaker
import ComputableAnalysis.GeometricRotationODE
import ComputableAnalysis.RotationPeanoBakerBridge
import ComputableAnalysis.FiniteNBallVolume
import ComputableAnalysis.FiniteGaussianIntegral
import ComputableAnalysis.ComplexCircleBridge
import ComputableAnalysis.ComplexPathIntegral
import ComputableAnalysis.FiniteComplexPathCertificate

/-!
# Computable calculus foundation

This is the focused public entry point for the project's calculus route.  It
collects the rational-circle, finite-integral, effective-FTC, power-series,
exponential/logarithm, Fourier, and scalar/linear-ODE interfaces without
requiring users to import the full benchmark catalogue in `ComputableAnalysis`.

The imports expose certificates and raw algorithms; they do not introduce a
completed real-number or measurable-function foundation.
-/

namespace ComputableAnalysis.ComplexPathIntegral

/-! Public complex FTC entry point for finite polygonal paths.  The path is a
finite list of rational-complex vertices and the primitive is supplied by its
finite polynomial coefficients, so the theorem is entirely algebraic. -/
theorem effectivePolynomialPathFTC
    (coefficients : List QComplex) (start endpoint : QComplex)
    (vertices : List QComplex) :
    (polygonalPolynomialIntegralRaw coefficients start
      (vertices ++ [endpoint])).Equiv
      (ComplexRaw.ofQComplex
        (polynomialPrimitiveIncrement coefficients start endpoint)) := by
  exact polygonalPolynomialIntegralRaw_equiv_endpoint
    coefficients start endpoint vertices

end ComputableAnalysis.ComplexPathIntegral

namespace ComputableAnalysis

/-! The finite secant product rule is the algebraic product-rule interface for
the effective calculus.  It is stated over rational endpoint values and a
positive cell, before any derivative or limit representation is introduced. -/
theorem effectiveSecantProductRule
    {x y f0 f1 g0 g1 : Rat} (hxy : x < y) :
    (f1 * g1 - f0 * g0) / (y - x) =
      f0 * ((g1 - g0) / (y - x)) +
        g1 * ((f1 - f0) / (y - x)) := by
  exact secantSlope_product_transport hxy

end ComputableAnalysis
