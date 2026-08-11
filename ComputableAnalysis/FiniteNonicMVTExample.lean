import ComputableAnalysis.PolynomialMeanValue

/-!
# A worked finite nonic Mean Value certificate

The polynomial `x^9` is evaluated on two rational intervals.  Its endpoint
secants and derivative endpoint brackets are exact finite rational data; no
intermediate real point or limiting theorem is selected.
-/

namespace ComputableAnalysis

open Polynomial

def nonicWorkedCoeffs : List Rat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem nonic_worked_coefficients_nonnegative :
    forall c, c ∈ nonicWorkedCoeffs -> 0 <= c := by
  intro c hc
  simp [nonicWorkedCoeffs] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    native_decide

theorem nonic_worked_secant_unit_interval :
    ExactFunction.differenceQuotient
        (fun z => eval nonicWorkedCoeffs z) 0 (1 - 0) = 1 := by
  native_decide

theorem nonic_worked_secant_derivative_bracket :
    (0 : Rat) <=
        ExactFunction.differenceQuotient
          (fun z => eval nonicWorkedCoeffs z) 0 (1 - 0) /\
      ExactFunction.differenceQuotient
          (fun z => eval nonicWorkedCoeffs z) 0 (1 - 0) <= 9 := by
  constructor <;> native_decide

theorem nonic_worked_secant_shifted_unit_interval :
    ExactFunction.differenceQuotient
        (fun z => eval nonicWorkedCoeffs z) 1 (2 - 1) = 511 := by
  native_decide

theorem nonic_worked_shifted_secant_derivative_bracket :
    (9 : Rat) <=
        ExactFunction.differenceQuotient
          (fun z => eval nonicWorkedCoeffs z) 1 (2 - 1) /\
      ExactFunction.differenceQuotient
          (fun z => eval nonicWorkedCoeffs z) 1 (2 - 1) <= 2304 := by
  constructor <;> native_decide

end ComputableAnalysis
