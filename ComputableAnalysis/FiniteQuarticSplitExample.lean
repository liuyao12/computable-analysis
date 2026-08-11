import ComputableAnalysis.FiniteQuarticQuadraticSplit

/-!
# A worked finite quartic split

The two supplied quadratic factors are `z^2 - 1` and `z^2 - 4`.  Their
product is a rational-coordinate quartic with four explicit roots; the
certificate uses the generic two-quadratic split theorem rather than a
completed Ferrari formula.
-/

namespace ComputableAnalysis

def quarticSplitOne : QComplex := { re := 1, im := 0 }
def quarticSplitMinusOne : QComplex := { re := -1, im := 0 }
def quarticSplitZero : QComplex := { re := 0, im := 0 }
def quarticSplitMinusFour : QComplex := { re := -4, im := 0 }
def quarticSplitTwo : QComplex := { re := 2, im := 0 }
def quarticSplitMinusTwo : QComplex := { re := -2, im := 0 }

theorem quartic_split_example_roots :
    CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitOne ∧
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitMinusOne ∧
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitTwo ∧
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitMinusTwo := by
  apply finiteQuarticQuadraticSplit_hasExactRoots
  all_goals
    simp [CPoly.hasExactRoot, qcomplexQuadraticPolynomial, CPoly.eval,
      QComplex.add, QComplex.mul, QComplex.zero, quarticSplitOne,
      quarticSplitMinusOne, quarticSplitZero, quarticSplitMinusFour,
      quarticSplitTwo, quarticSplitMinusTwo] <;> native_decide

theorem quartic_split_example_certificate :
    CPoly.eval
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitOne = QComplex.zero ∧
      CPoly.eval
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitTwo = QComplex.zero := by
  constructor <;> native_decide

end ComputableAnalysis
