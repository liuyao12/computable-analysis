import ComputableAnalysis.PolynomialMeanValue

/-!
# A worked finite quintic Mean Value certificate

The polynomial `x^5` has secant slope `1` on `[0,1]`, while its finite
derivative evaluator ranges from `0` to `5`.  This is a rational endpoint
certificate; it does not choose an intermediate real point.
-/

namespace ComputableAnalysis

open Polynomial

def quinticWorkedCoeffs : List Rat := [0, 0, 0, 0, 0, 1]

theorem quintic_worked_coefficients_nonnegative :
    forall c, c ∈ quinticWorkedCoeffs -> 0 <= c := by
  intro c hc
  simp [quinticWorkedCoeffs] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

theorem quintic_worked_secant_unit_interval :
    ExactFunction.differenceQuotient
        (fun z => eval quinticWorkedCoeffs z) 0 (1 - 0) = 1 := by
  native_decide

theorem quintic_worked_secant_derivative_bracket :
    (0 : Rat) <=
        ExactFunction.differenceQuotient
          (fun z => eval quinticWorkedCoeffs z) 0 (1 - 0) /\
      ExactFunction.differenceQuotient
          (fun z => eval quinticWorkedCoeffs z) 0 (1 - 0) <= 5 := by
  constructor <;> native_decide

theorem quintic_worked_generic_bracket :
    (0 : Rat) <=
        ExactFunction.differenceQuotient
          (fun z => eval quinticWorkedCoeffs z) 0 (1 - 0) /\
      ExactFunction.differenceQuotient
          (fun z => eval quinticWorkedCoeffs z) 0 (1 - 0) <= 5 := by
  have h := Polynomial.finiteQuintic_secant_derivative_bracket
      (c₀ := 0) (c₁ := 0) (c₂ := 0) (c₃ := 0) (c₄ := 0) (c₅ := 1)
      (a := 0) (b := 1) quintic_worked_coefficients_nonnegative (by native_decide)
      (by native_decide) (by native_decide)
  constructor
  · calc
      (0 : Rat) = 0 + 2 * 0 * 0 + 3 * 0 * 0 ^ 2 +
          4 * 0 * 0 ^ 3 + 5 * 1 * 0 ^ 4 := by native_decide
      _ <= ExactFunction.differenceQuotient
          (fun z => eval [0, 0, 0, 0, 0, 1] z) 0 (1 - 0) := h.1
  · calc
      ExactFunction.differenceQuotient
          (fun z => eval [0, 0, 0, 0, 0, 1] z) 0 (1 - 0) <=
          0 + 2 * 0 * 1 + 3 * 0 * 1 ^ 2 +
            4 * 0 * 1 ^ 3 + 5 * 1 * 1 ^ 4 := h.2
      _ = 5 := by native_decide

end ComputableAnalysis
