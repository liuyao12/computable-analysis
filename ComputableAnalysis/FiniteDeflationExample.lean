import ComputableAnalysis.FiniteDeflationChain

/-!
# A concrete supplied-root deflation chain

The cubic `z^3 - 6 z^2 + 11 z - 6` is deflated at the supplied rational roots
`1`, `2`, and `3`.  Every step is finite synthetic division; the example does
not claim that roots can be found without being supplied.
-/

namespace ComputableAnalysis

namespace FiniteDeflationExample

open FiniteFTABoundary
open FiniteDeflationChain

def cubic : CPoly.Coeffs :=
  [QComplex.ofRat (-6), QComplex.ofRat 11, QComplex.ofRat (-6), QComplex.one]

def rootOne : QComplex := QComplex.ofRat 1
def rootTwo : QComplex := QComplex.ofRat 2
def rootThree : QComplex := QComplex.ofRat 3

theorem cubic_root_one : CPoly.eval cubic rootOne = QComplex.zero := by
  native_decide

theorem cubic_deflation_one :
    (syntheticDivide rootOne cubic).1 =
      [QComplex.ofRat 6, QComplex.ofRat (-5), QComplex.one, QComplex.zero] := by
  native_decide

theorem cubic_deflation_one_remainder :
    (syntheticDivide rootOne cubic).2 = QComplex.zero := by
  rw [syntheticDivide_remainder_eq_eval, cubic_root_one]

theorem cubic_factor_at_one :
    CPoly.eval cubic x =
      QComplex.mul (QComplex.sub x rootOne)
        (CPoly.eval (syntheticDivide rootOne cubic).1 x) := by
  exact syntheticDivide_factor_of_root (x := x) cubic_root_one

theorem cubic_deflation_chain :
    IsDeflationChain cubic [rootOne, rootTwo, rootThree] := by
  constructor
  · exact cubic_root_one
  constructor
  · rw [← syntheticDivide_remainder_eq_zero_iff]
    native_decide
  constructor
  · rw [← syntheticDivide_remainder_eq_zero_iff]
    native_decide
  · trivial

theorem cubic_deflated_coeffs :
    deflatedCoeffs cubic [rootOne, rootTwo, rootThree] =
      [QComplex.one, QComplex.zero, QComplex.zero, QComplex.zero] := by
  native_decide

theorem cubic_horner_factorization (x : QComplex) :
    CPoly.eval cubic x =
      QComplex.mul (rootFactorProduct [rootOne, rootTwo, rootThree] x)
        (CPoly.eval (deflatedCoeffs cubic [rootOne, rootTwo, rootThree]) x) := by
  exact horner_factorization cubic [rootOne, rootTwo, rootThree] x
    cubic_deflation_chain

end FiniteDeflationExample

end ComputableAnalysis
