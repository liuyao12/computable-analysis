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

def complexPrimitiveCoefficients (coefficients : Nat -> QComplex) : Nat -> QComplex
  | 0 => QComplex.zero
  | k + 1 =>
      QComplex.scaleRat (1 / (((k + 1 : Nat) : Rat))) (coefficients k)

def complexCoefficientDerivative (coefficients : Nat -> QComplex) : Nat -> QComplex :=
  fun k => QComplex.scaleRat (((k + 1 : Nat) : Rat)) (coefficients (k + 1))

private theorem qcomplex_scaleRat_nat_inv (k : Nat) (z : QComplex) :
    QComplex.scaleRat (((k + 1 : Nat) : Rat))
        (QComplex.scaleRat (1 / (((k + 1 : Nat) : Rat))) z) = z := by
  rw [QComplex.scaleRat_scaleRat]
  have hk : (((k + 1 : Nat) : Rat)) ≠ 0 := by
    exact FormalPowerSeries.natCast_succ_ne_zero k
  have hcancel :
      (((k + 1 : Nat) : Rat)) * (1 / (((k + 1 : Nat) : Rat))) = 1 := by
    rw [Rat.div_def]
    simp only [Rat.one_mul]
    rw [Rat.mul_comm]
    exact Rat.inv_mul_cancel _ hk
  rw [hcancel]
  cases z <;> simp [QComplex.scaleRat]

theorem complexCoefficientDerivative_primitiveCoefficients
    (coefficients : Nat -> QComplex) :
    complexCoefficientDerivative (complexPrimitiveCoefficients coefficients) =
      coefficients := by
  funext k
  cases k with
  | zero =>
      simpa [complexCoefficientDerivative, complexPrimitiveCoefficients] using
        qcomplex_scaleRat_nat_inv 0 (coefficients 0)
  | succ k =>
      simpa [complexCoefficientDerivative, complexPrimitiveCoefficients,
        Rat.natCast_add] using
        qcomplex_scaleRat_nat_inv (k + 1) (coefficients (k + 1))

theorem complexFinitePrimitivePrefix_succ
    (coefficients : Nat -> QComplex) (z : QComplex) (terms : Nat) :
    complexFinitePrimitivePrefix coefficients z (terms + 1) =
      QComplex.add
        (complexFinitePrimitivePrefix coefficients z terms)
        (complexFinitePrimitiveTerm coefficients z terms) := by
  simp [complexFinitePrimitivePrefix, List.range_succ, List.foldl_append]

private theorem qcomplex_sub_add_sub (a b c d : QComplex) :
    QComplex.sub (QComplex.add a b) (QComplex.add c d) =
      QComplex.add (QComplex.sub a c) (QComplex.sub b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero] <;>
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem qcomplex_scale_mul_sub (r : Rat) (c z w : QComplex) :
    QComplex.sub (QComplex.scaleRat r (QComplex.mul c z))
        (QComplex.scaleRat r (QComplex.mul c w)) =
      QComplex.scaleRat r (QComplex.mul c (QComplex.sub z w)) := by
  cases r <;> cases c <;> cases z <;> cases w <;>
    simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.scaleRat,
      QComplex.mul] <;>
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.add_left_comm]

theorem complexFinitePrimitivePrefix_endpointDifference
    (coefficients : Nat -> QComplex) (z w : QComplex) (terms : Nat) :
    QComplex.sub
        (complexFinitePrimitivePrefix coefficients z terms)
        (complexFinitePrimitivePrefix coefficients w terms) =
      (List.range terms).foldl
        (fun acc k => QComplex.add acc
          (QComplex.scaleRat (1 / (((k + 1 : Nat) : Rat)))
            (QComplex.mul (coefficients k)
              (QComplex.sub (QComplex.pow z (k + 1))
                (QComplex.pow w (k + 1)))))) QComplex.zero := by
  induction terms with
  | zero =>
      simp [complexFinitePrimitivePrefix, QComplex.sub, QComplex.add,
        QComplex.neg, QComplex.zero, Rat.zero_add, Rat.add_zero]
  | succ terms ih =>
      rw [complexFinitePrimitivePrefix_succ, complexFinitePrimitivePrefix_succ]
      rw [qcomplex_sub_add_sub]
      rw [ih]
      have hterm :
          QComplex.sub (complexFinitePrimitiveTerm coefficients z terms)
              (complexFinitePrimitiveTerm coefficients w terms) =
            QComplex.scaleRat (1 / (((terms + 1 : Nat) : Rat)))
              (QComplex.mul (coefficients terms)
                (QComplex.sub (QComplex.pow z (terms + 1))
                  (QComplex.pow w (terms + 1)))) := by
        unfold complexFinitePrimitiveTerm
        exact qcomplex_scale_mul_sub _ _ _ _
      rw [hterm]
      simp [List.range_succ, List.foldl_append]

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
