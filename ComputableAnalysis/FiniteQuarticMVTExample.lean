import ComputableAnalysis.PolynomialMeanValue
import ComputableAnalysis.FiniteBisectionIteration

/-!
# A worked finite quartic Mean Value certificate

The polynomial `x^4` has secant slope `1` on `[0,1]`, while its finite
derivative evaluator is bracketed by `0` and `4`.  This is a rational endpoint
certificate and does not select an intermediate real point.
-/

namespace ComputableAnalysis

open Polynomial

def quarticWorkedCoeffs : List Rat := [0, 0, 0, 0, 1]

def quarticUnitNormalizedDerivativeAverage : Rat := 1 / 4

def quarticUnitDerivativeTarget : Rat -> Rat := fun x => x ^ 3

theorem quarticUnitNormalizedDerivativeAverage_in_unit :
    0 <= quarticUnitNormalizedDerivativeAverage /\
      quarticUnitNormalizedDerivativeAverage <= 1 := by
  unfold quarticUnitNormalizedDerivativeAverage
  native_decide

theorem quarticUnit_secant_eq_four_mul_normalizedDerivativeAverage :
    ExactFunction.differenceQuotient
        (fun z => eval quarticWorkedCoeffs z) 0 (1 - 0) =
      4 * quarticUnitNormalizedDerivativeAverage := by
  unfold quarticWorkedCoeffs quarticUnitNormalizedDerivativeAverage
  native_decide

theorem quarticUnit_mvt_bisection_tolerance_certificate (eps : QPos) :
    let J := monotoneTargetBisectionIterate
      quarticUnitDerivativeTarget quarticUnitNormalizedDerivativeAverage
      eps.val.den { lo := 0, hi := 1 }
    J.lo <= J.hi /\
      (quarticUnitDerivativeTarget J.lo <=
          quarticUnitNormalizedDerivativeAverage /\
        quarticUnitNormalizedDerivativeAverage <=
          quarticUnitDerivativeTarget J.hi) /\
      (J.lo >= 0 /\ J.hi <= 1) /\
      J.width <= eps.val := by
  simpa [quarticUnitDerivativeTarget,
    quarticUnitNormalizedDerivativeAverage] using
    (monotoneTargetBisectionIterate_tolerance_certificate
      (f := quarticUnitDerivativeTarget)
      (I := ({ lo := 0, hi := 1 } : QInterval))
      quarticUnitNormalizedDerivativeAverage
      (by native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)
      eps)

theorem quartic_worked_coefficients_nonnegative :
    forall c, c ∈ quarticWorkedCoeffs -> 0 <= c := by
  intro c hc
  simp [quarticWorkedCoeffs] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    native_decide

theorem quartic_worked_secant_unit_interval :
    ExactFunction.differenceQuotient
        (fun z => eval quarticWorkedCoeffs z) 0 (1 - 0) = 1 := by
  native_decide

theorem quartic_worked_secant_derivative_bracket :
    (0 : Rat) <=
        ExactFunction.differenceQuotient
          (fun z => eval quarticWorkedCoeffs z) 0 (1 - 0) /\
      ExactFunction.differenceQuotient
          (fun z => eval quarticWorkedCoeffs z) 0 (1 - 0) <= 4 := by
  constructor <;> native_decide

end ComputableAnalysis
