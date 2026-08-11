import ComputableAnalysis.FTA

/-!
# A worked supplied-root quintic certificate

The factorized quintic with roots `-2,-1,0,1,2` provides five exact rational
complex root witnesses.  This is the finite supplied-root boundary associated
with Abel--Ruffini, not a general quintic solver or a radicals formula.
-/

namespace ComputableAnalysis

def quinticBoundaryMinusTwo : QComplex := { re := -2, im := 0 }
def quinticBoundaryMinusOne : QComplex := { re := -1, im := 0 }
def quinticBoundaryZero : QComplex := { re := 0, im := 0 }
def quinticBoundaryOne : QComplex := { re := 1, im := 0 }
def quinticBoundaryTwo : QComplex := { re := 2, im := 0 }

theorem quintic_boundary_example_roots :
    CPoly.hasExactRoot
        (factorizedQuinticPolynomial quinticBoundaryMinusTwo
          quinticBoundaryMinusOne quinticBoundaryZero quinticBoundaryOne
          quinticBoundaryTwo) quinticBoundaryMinusTwo ∧
      CPoly.hasExactRoot
        (factorizedQuinticPolynomial quinticBoundaryMinusTwo
          quinticBoundaryMinusOne quinticBoundaryZero quinticBoundaryOne
          quinticBoundaryTwo) quinticBoundaryMinusOne ∧
      CPoly.hasExactRoot
        (factorizedQuinticPolynomial quinticBoundaryMinusTwo
          quinticBoundaryMinusOne quinticBoundaryZero quinticBoundaryOne
          quinticBoundaryTwo) quinticBoundaryZero ∧
      CPoly.hasExactRoot
        (factorizedQuinticPolynomial quinticBoundaryMinusTwo
          quinticBoundaryMinusOne quinticBoundaryZero quinticBoundaryOne
          quinticBoundaryTwo) quinticBoundaryOne ∧
      CPoly.hasExactRoot
        (factorizedQuinticPolynomial quinticBoundaryMinusTwo
          quinticBoundaryMinusOne quinticBoundaryZero quinticBoundaryOne
          quinticBoundaryTwo) quinticBoundaryTwo := by
  repeat' apply And.intro
  all_goals
    apply (factorizedQuinticPolynomial_hasExactRoot_iff_mem
      quinticBoundaryMinusTwo quinticBoundaryMinusOne quinticBoundaryZero
      quinticBoundaryOne quinticBoundaryTwo _).2
    simp

end ComputableAnalysis
