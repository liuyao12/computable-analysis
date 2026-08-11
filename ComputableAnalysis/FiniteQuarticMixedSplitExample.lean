import ComputableAnalysis.FiniteQuarticQuadraticSplit

/-!
# A worked mixed real/complex quartic split

The supplied factors are `z^2 + 1` and `z^2 - 4`.  Their product has the
rational-coordinate roots `i`, `-i`, `2`, and `-2`.  This is a finite
two-quadratic certificate with a nonreal branch; it does not invoke a general
quartic formula or an algebraic-closure theorem.
-/

namespace ComputableAnalysis

def quarticMixedImaginary : QComplex := { re := 0, im := 1 }
def quarticMixedMinusImaginary : QComplex := { re := 0, im := -1 }
def quarticMixedTwo : QComplex := { re := 2, im := 0 }
def quarticMixedMinusTwo : QComplex := { re := -2, im := 0 }

theorem quartic_mixed_split_example_roots :
    CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 1, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -4, im := 0 })
        quarticMixedImaginary ∧
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 1, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -4, im := 0 })
        quarticMixedMinusImaginary ∧
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 1, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -4, im := 0 })
        quarticMixedTwo ∧
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 1, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -4, im := 0 })
        quarticMixedMinusTwo := by
  apply finiteQuarticQuadraticSplit_hasExactRoots
  all_goals
    simp [CPoly.hasExactRoot, qcomplexQuadraticPolynomial, CPoly.eval,
      QComplex.add, QComplex.mul, QComplex.zero, quarticMixedImaginary,
      quarticMixedMinusImaginary, quarticMixedTwo, quarticMixedMinusTwo] <;>
      native_decide

theorem quartic_mixed_split_example_certificate :
    CPoly.eval
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 1, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -4, im := 0 })
        quarticMixedImaginary = QComplex.zero ∧
      CPoly.eval
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 1, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -4, im := 0 })
        quarticMixedTwo = QComplex.zero := by
  constructor <;> native_decide

def quarticMixedScaledTwoImaginary : QComplex := { re := 0, im := 2 }
def quarticMixedScaledMinusTwoImaginary : QComplex := { re := 0, im := -2 }
def quarticMixedScaledThree : QComplex := { re := 3, im := 0 }
def quarticMixedScaledMinusThree : QComplex := { re := -3, im := 0 }

theorem quartic_mixed_scaled_split_example_roots :
    CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 4, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -9, im := 0 })
        quarticMixedScaledTwoImaginary /\
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 4, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -9, im := 0 })
        quarticMixedScaledMinusTwoImaginary /\
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 4, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -9, im := 0 })
        quarticMixedScaledThree /\
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 4, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -9, im := 0 })
        quarticMixedScaledMinusThree := by
  apply finiteQuarticQuadraticSplit_hasExactRoots
  all_goals
    simp [CPoly.hasExactRoot, qcomplexQuadraticPolynomial, CPoly.eval,
      QComplex.add, QComplex.mul, QComplex.zero,
      quarticMixedScaledTwoImaginary,
      quarticMixedScaledMinusTwoImaginary,
      quarticMixedScaledThree, quarticMixedScaledMinusThree] <;>
      native_decide

theorem quartic_mixed_scaled_split_example_certificate :
    CPoly.eval
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 4, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -9, im := 0 })
        quarticMixedScaledTwoImaginary = QComplex.zero /\
      CPoly.eval
        (finiteQuarticQuadraticSplit
          { re := 1, im := 0 } { re := 0, im := 0 } { re := 4, im := 0 }
          { re := 1, im := 0 } { re := 0, im := 0 } { re := -9, im := 0 })
        quarticMixedScaledThree = QComplex.zero := by
  constructor <;> native_decide

end ComputableAnalysis
