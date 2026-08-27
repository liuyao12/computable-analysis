import ComputableAnalysis.PowerSeries
import ComputableAnalysis.Series
import ComputableAnalysis.FirstYearCalculus
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.FiniteSineIntegral
import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.FiniteFourierOrthogonality
import ComputableAnalysis.FiniteFourierEnergy
import ComputableAnalysis.EffectiveFourierSeries
import ComputableAnalysis.EffectiveFourierTail
import ComputableAnalysis.FiniteNBallVolume
import ComputableAnalysis.FiniteGaussianIntegral

/-!
# Finite series and Fourier foundation

This scoped entry point collects the rational coefficient, finite-prefix,
Fourier-tail, Gaussian-prefix, and finite ball-volume interfaces.  It exposes
computable series certificates without importing the full benchmark catalogue
or introducing a completed function space.
-/

namespace ComputableAnalysis

/-! Project-facing names for the finite termwise-FTC bridge.  These are exact
rational identities for finite prefixes; convergence and tail transport are
separate certificates. -/
theorem effectiveFiniteTaylorFTC_prefix
    (coeffs : Nat -> Rat) (terms : Nat) (a b : Rat) :
    FinitePolynomial.integratedTaylorPrefix coeffs terms b -
        FinitePolynomial.integratedTaylorPrefix coeffs terms a =
      (List.range terms).foldl
        (fun acc k => acc + coeffs k *
          (b ^ (k + 1) / ((k + 1 : Nat) : Rat) -
            a ^ (k + 1) / ((k + 1 : Nat) : Rat))) 0 := by
  exact FinitePolynomial.finiteTaylorFTC_prefix coeffs terms a b

/-! The complex exponential and trigonometric primitive laws are exported
alongside the finite Taylor law.  They concern only rational-complex prefixes
and therefore do not invoke a completed complex function space. -/
theorem effectiveExpIntegratedPartial_eq_expPartial_sub_one
    (z : QComplex) (n : Nat) :
    ComplexSeries.expIntegratedPartial z n =
      QComplex.sub (ComplexSeries.expPartial z (n + 1)) QComplex.one := by
  exact ComplexSeries.expIntegratedPartial_eq_expPartial_sub_one z n

theorem effectiveSinIntegratedPartial_eq_one_sub_cosPartial
    (z : QComplex) (n : Nat) :
    ComplexSeries.sinIntegratedPartial z n =
      QComplex.sub QComplex.one (ComplexSeries.cosPartial z (n + 1)) := by
  exact ComplexSeries.sinIntegratedPartial_eq_one_sub_cosPartial z n

theorem effectiveCosIntegratedPartial_eq_sinPartial
    (z : QComplex) (n : Nat) :
    ComplexSeries.cosIntegratedPartial z n =
      ComplexSeries.sinPartial z n := by
  exact ComplexSeries.cosIntegratedPartial_eq_sinPartial z n

end ComputableAnalysis
