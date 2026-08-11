import ComputableAnalysis.FTA

/-!
# A worked mixed real/complex cubic certificate

The factorization `(z - 1)(z - i)(z + i)` gives the finite rational-complex
cubic `z^3 - z^2 + z - 1`.  Its three supplied roots include a conjugate
nonreal pair; no general cubic formula or algebraic-closure theorem is used.
-/

namespace ComputableAnalysis

def mixedCubicOne : QComplex := { re := 1, im := 0 }
def mixedCubicImaginary : QComplex := { re := 0, im := 1 }
def mixedCubicMinusImaginary : QComplex := { re := 0, im := -1 }

def mixedCubicPolynomial : CPoly.Coeffs :=
  factorizedCubicPolynomial mixedCubicOne mixedCubicImaginary
    mixedCubicMinusImaginary

theorem mixedCubicPolynomial_coefficients :
    mixedCubicPolynomial =
      [{ re := -1, im := 0 }, { re := 1, im := 0 },
        { re := -1, im := 0 }, { re := 1, im := 0 }] := by
  native_decide

theorem mixed_cubic_example_roots :
    CPoly.hasExactRoot mixedCubicPolynomial mixedCubicOne ∧
      CPoly.hasExactRoot mixedCubicPolynomial mixedCubicImaginary ∧
      CPoly.hasExactRoot mixedCubicPolynomial mixedCubicMinusImaginary := by
  constructor
  · simpa [mixedCubicPolynomial] using
      (factorizedCubic_left_exact_root mixedCubicOne mixedCubicImaginary
        mixedCubicMinusImaginary)
  constructor
  · simpa [mixedCubicPolynomial] using
      (factorizedCubic_middle_exact_root mixedCubicOne mixedCubicImaginary
        mixedCubicMinusImaginary)
  · simpa [mixedCubicPolynomial] using
      (factorizedCubic_right_exact_root mixedCubicOne mixedCubicImaginary
        mixedCubicMinusImaginary)

theorem mixed_cubic_example_explicit_certificate :
    CPoly.eval mixedCubicPolynomial mixedCubicOne = QComplex.zero ∧
      CPoly.eval mixedCubicPolynomial mixedCubicImaginary = QComplex.zero ∧
      CPoly.eval mixedCubicPolynomial mixedCubicMinusImaginary = QComplex.zero := by
  native_decide

def mixedCubicTwo : QComplex := { re := 2, im := 0 }
def mixedCubicTwoImaginary : QComplex := { re := 0, im := 2 }
def mixedCubicTwoMinusImaginary : QComplex := { re := 0, im := -2 }

def mixedCubicTwoPolynomial : CPoly.Coeffs :=
  factorizedCubicPolynomial mixedCubicTwo mixedCubicTwoImaginary
    mixedCubicTwoMinusImaginary

theorem mixedCubicTwoPolynomial_coefficients :
    mixedCubicTwoPolynomial =
      [{ re := -8, im := 0 }, { re := 4, im := 0 },
        { re := -2, im := 0 }, { re := 1, im := 0 }] := by
  native_decide

theorem mixed_cubic_two_example_roots :
    CPoly.hasExactRoot mixedCubicTwoPolynomial mixedCubicTwo /\
      CPoly.hasExactRoot mixedCubicTwoPolynomial mixedCubicTwoImaginary /\
      CPoly.hasExactRoot mixedCubicTwoPolynomial mixedCubicTwoMinusImaginary := by
  constructor
  · simpa [mixedCubicTwoPolynomial] using
      (factorizedCubic_left_exact_root mixedCubicTwo mixedCubicTwoImaginary
        mixedCubicTwoMinusImaginary)
  constructor
  · simpa [mixedCubicTwoPolynomial] using
      (factorizedCubic_middle_exact_root mixedCubicTwo mixedCubicTwoImaginary
        mixedCubicTwoMinusImaginary)
  · simpa [mixedCubicTwoPolynomial] using
      (factorizedCubic_right_exact_root mixedCubicTwo mixedCubicTwoImaginary
        mixedCubicTwoMinusImaginary)

theorem mixed_cubic_two_example_explicit_certificate :
    CPoly.eval mixedCubicTwoPolynomial mixedCubicTwo = QComplex.zero /\
      CPoly.eval mixedCubicTwoPolynomial mixedCubicTwoImaginary = QComplex.zero /\
      CPoly.eval mixedCubicTwoPolynomial mixedCubicTwoMinusImaginary =
        QComplex.zero := by
  native_decide

end ComputableAnalysis
