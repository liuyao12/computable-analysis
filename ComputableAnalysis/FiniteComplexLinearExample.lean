import ComputableAnalysis.FTA

/-!
# A worked finite complex-linear FTA certificate

The constant-first polynomial `-2 + (1+i) z` has the rational-coordinate root
`1-i`.  Lean checks both the supplied inverse witness and the exact Horner
evaluation, without invoking a completed complex field.
-/

namespace ComputableAnalysis

def finiteComplexLinear : CPoly.Coeffs :=
  [QComplex.ofRat (-2), { re := 1, im := 1 }]

def finiteComplexLinearInverse : QComplex := { re := 1 / 2, im := -(1 / 2) }

def finiteComplexLinearRoot : QComplex := { re := 1, im := -1 }

theorem finiteComplexLinear_leading_inverse :
    QComplex.mul ({ re := 1, im := 1 } : QComplex)
        finiteComplexLinearInverse = QComplex.one := by
  native_decide

theorem finiteComplexLinear_root_eval :
    CPoly.eval finiteComplexLinear finiteComplexLinearRoot = QComplex.zero := by
  native_decide

theorem finiteComplexLinear_root_from_inverse :
    CPoly.hasExactRoot finiteComplexLinear finiteComplexLinearRoot := by
  change CPoly.eval finiteComplexLinear finiteComplexLinearRoot = QComplex.zero
  native_decide

end ComputableAnalysis
