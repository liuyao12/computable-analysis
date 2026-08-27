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

namespace ComputableAnalysis.ExactFunction

/-! Public finite chain-rule factorization and error estimate.  The nonzero
inner increment is explicit, so this is a rational forward-step theorem rather
than an assertion about an attained derivative at a limit point. -/
theorem effectiveDifferenceQuotientCompositionFactorization
    (f g : Rat -> Rat) {x h : Rat}
    (hh : h ≠ 0)
    (hgh : g (x + h) - g x ≠ 0) :
    differenceQuotient (fun z => f (g z)) x h =
      differenceQuotient f (g x) (g (x + h) - g x) *
        differenceQuotient g x h := by
  exact differenceQuotient_comp_factorization f g hh hgh

theorem effectiveDifferenceQuotientCompositionErrorLe
    (f df g dg : Rat -> Rat) {x h : Rat}
    (hh : h ≠ 0)
    (hgh : g (x + h) - g x ≠ 0) :
    qabs (differenceQuotient (fun z => f (g z)) x h -
      df (g x) * dg x) <=
      qabs (differenceQuotient f (g x) (g (x + h) - g x)) *
          qabs (differenceQuotient g x h - dg x) +
        qabs (dg x) *
          qabs (differenceQuotient f (g x) (g (x + h) - g x) -
            df (g x)) := by
  exact differenceQuotient_comp_error_le f df g dg hh hgh

end ComputableAnalysis.ExactFunction

namespace ComputableAnalysis

/-! Public finite integration-by-parts and square-chain identities.  The
quadratic-variation term is retained explicitly, so the finite statement does
not rely on silently discarding a mesh error. -/
theorem effectiveFiniteIntegrationByParts
    (f g : Nat -> Rat) (n : Nat) :
    leftStieltjesSum f g n + rightStieltjesSum f g n =
      f n * g n - f 0 * g 0 := by
  exact finiteIntegrationByParts f g n

theorem effectiveFiniteSquareChain
    (f : Nat -> Rat) (n : Nat) :
    2 * leftStieltjesSum f f n + quadraticVariationSum f f n =
      f n * f n - f 0 * f 0 := by
  exact finiteSquareStieltjes_chain f n

theorem effectiveFiniteSquareChain_left_bounds
    (f : Nat -> Rat) (n : Nat) (eps : Rat)
    (hvariation : 0 <= quadraticVariationSum f f n)
    (hvariation_le : quadraticVariationSum f f n <= eps) :
    f n * f n - f 0 * f 0 - eps <=
        2 * leftStieltjesSum f f n /\
      2 * leftStieltjesSum f f n <=
        f n * f n - f 0 * f 0 := by
  exact finiteSquareStieltjes_left_bounds f n eps hvariation hvariation_le

end ComputableAnalysis
