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

/-! A finite complex coefficient prefix has the same termwise primitive
constructor as the rational polynomial layer.  The coefficient stream and
the evaluation point are rational-complex, while division by the natural
index remains a rational scalar operation. -/
def complexFinitePrimitiveTerm
    (coefficients : Nat -> QComplex) (z : QComplex) (k : Nat) : QComplex :=
  QComplex.scaleRat (1 / (((k + 1 : Nat) : Rat)))
    (QComplex.mul (coefficients k) (QComplex.pow z (k + 1)))

def complexFinitePrimitivePrefix
    (coefficients : Nat -> QComplex) (z : QComplex) (terms : Nat) : QComplex :=
  (List.range terms).foldl
    (fun acc k => QComplex.add acc
      (complexFinitePrimitiveTerm coefficients z k)) QComplex.zero

theorem complexFinitePrimitivePrefix_succ
    (coefficients : Nat -> QComplex) (z : QComplex) (terms : Nat) :
    complexFinitePrimitivePrefix coefficients z (terms + 1) =
      QComplex.add
        (complexFinitePrimitivePrefix coefficients z terms)
        (complexFinitePrimitiveTerm coefficients z terms) := by
  simp [complexFinitePrimitivePrefix, List.range_succ, List.foldl_append]

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
