import ComputableAnalysis.FTA
import ComputableAnalysis.FiniteFTAConcreteCertificate

/-!
# A worked finite complex quadratic certificate

The polynomial `z^2 - 2z + 5` has the rational-coordinate complex roots
`1 + 2i` and `1 - 2i`.  Lean checks both exact Horner evaluations, their
distinctness, and the finite factorization identity.  This is a concrete
discriminant/root-witness instance; it does not assert global root existence
for arbitrary polynomials.
-/

namespace ComputableAnalysis

def finiteComplexQuadratic : CPoly.Coeffs :=
  [QComplex.ofRat 5, QComplex.ofRat (-2), QComplex.one]

def finiteComplexQuadraticUpper : QComplex := { re := 1, im := 2 }

def finiteComplexQuadraticLower : QComplex := { re := 1, im := -2 }

theorem finiteComplexQuadratic_upper_root :
    CPoly.eval finiteComplexQuadratic finiteComplexQuadraticUpper =
      QComplex.zero := by
  native_decide

theorem finiteComplexQuadratic_lower_root :
    CPoly.eval finiteComplexQuadratic finiteComplexQuadraticLower =
      QComplex.zero := by
  native_decide

theorem finiteComplexQuadratic_roots_distinct :
    finiteComplexQuadraticUpper ≠ finiteComplexQuadraticLower := by
  native_decide

theorem finiteComplexQuadratic_factorization (z : QComplex) :
    CPoly.eval finiteComplexQuadratic z =
      QComplex.mul
        (QComplex.sub z finiteComplexQuadraticUpper)
        (QComplex.sub z finiteComplexQuadraticLower) := by
  simp [finiteComplexQuadratic, finiteComplexQuadraticUpper,
    finiteComplexQuadraticLower, CPoly.eval, QComplex.ofRat,
    QComplex.one, QComplex.zero, QComplex.mul, QComplex.sub,
    QComplex.add, QComplex.neg]
  cases z
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem finiteComplexQuadratic_root_search_upper :
    exactRootSearch finiteComplexQuadratic
        [finiteComplexQuadraticUpper, finiteComplexQuadraticLower] =
      some finiteComplexQuadraticUpper := by
  native_decide

theorem finiteComplexQuadratic_root_search_sound :
    CPoly.hasExactRoot finiteComplexQuadratic finiteComplexQuadraticUpper := by
  apply exactRootSearch_sound finiteComplexQuadratic_root_search_upper

end ComputableAnalysis
