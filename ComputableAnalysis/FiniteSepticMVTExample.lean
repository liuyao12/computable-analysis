import ComputableAnalysis.PolynomialMeanValue

/-!
# A worked finite septic Mean Value certificate

The polynomial `x^7` is evaluated on the rational interval `[0,1]`.
Its endpoint secant is `1`, while the finite derivative evaluator ranges
from `0` to `7`.  This is a concrete degree-seven instance of the project's
finite Mean Value interface; it does not select an intermediate point or use
a completed real interval.
-/

namespace ComputableAnalysis

open Polynomial

def septicWorkedCoeffs : List Rat := [0, 0, 0, 0, 0, 0, 0, 1]

theorem septic_worked_coefficients_nonnegative :
    forall c, c ∈ septicWorkedCoeffs -> 0 <= c := by
  intro c hc
  simp [septicWorkedCoeffs] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

theorem septic_worked_secant_unit_interval :
    ExactFunction.differenceQuotient
        (fun z => eval septicWorkedCoeffs z) 0 (1 - 0) = 1 := by
  native_decide

theorem septic_worked_derivative_endpoints :
    (0 : Rat) <=
        (0 + 2 * 0 * 0 + 3 * 0 * 0 ^ 2 + 4 * 0 * 0 ^ 3 +
          5 * 0 * 0 ^ 4 + 6 * 0 * 0 ^ 5 + 7 * 1 * 0 ^ 6) /\
      (0 + 2 * 0 * 1 + 3 * 0 * 1 ^ 2 + 4 * 0 * 1 ^ 3 +
          5 * 0 * 1 ^ 4 + 6 * 0 * 1 ^ 5 + 7 * 1 * 1 ^ 6) = 7 := by
  native_decide

theorem septic_worked_secant_derivative_bracket :
    (0 : Rat) <=
        ExactFunction.differenceQuotient
          (fun z => eval septicWorkedCoeffs z) 0 (1 - 0) /\
      ExactFunction.differenceQuotient
          (fun z => eval septicWorkedCoeffs z) 0 (1 - 0) <= 7 := by
  constructor
  · native_decide
  · native_decide

theorem septic_worked_secant_shifted_unit_interval :
    ExactFunction.differenceQuotient
        (fun z => eval septicWorkedCoeffs z) 1 (2 - 1) = 127 := by
  native_decide

theorem septic_worked_derivative_shifted_endpoints :
    (7 : Rat) <=
        (0 + 2 * 0 * 1 + 3 * 0 * 1 ^ 2 + 4 * 0 * 1 ^ 3 +
          5 * 0 * 1 ^ 4 + 6 * 0 * 1 ^ 5 + 7 * 1 * 1 ^ 6) /\
      (0 + 2 * 0 * 2 + 3 * 0 * 2 ^ 2 + 4 * 0 * 2 ^ 3 +
          5 * 0 * 2 ^ 4 + 6 * 0 * 2 ^ 5 + 7 * 1 * 2 ^ 6) = 448 := by
  native_decide

theorem septic_worked_shifted_secant_derivative_bracket :
    (7 : Rat) <=
        ExactFunction.differenceQuotient
          (fun z => eval septicWorkedCoeffs z) 1 (2 - 1) /\
      ExactFunction.differenceQuotient
          (fun z => eval septicWorkedCoeffs z) 1 (2 - 1) <= 448 := by
  constructor
  · native_decide
  · native_decide

end ComputableAnalysis
