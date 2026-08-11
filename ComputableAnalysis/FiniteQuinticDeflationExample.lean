import ComputableAnalysis.FiniteQuinticBoundaryExample
import ComputableAnalysis.FiniteDeflationChain

/-!
# A supplied-root quintic deflation chain

The factorized quintic with roots `-2,-1,0,1,2` is peeled one supplied root
at a time.  The preservation lemma for distinct roots transports each later
root to the next quotient.  This is a finite Abel--Ruffini boundary: it does
not construct roots, radicals, or a general quintic solver.
-/

namespace ComputableAnalysis

open FiniteDeflationChain

def quinticBoundaryPolynomial : CPoly.Coeffs :=
  factorizedQuinticPolynomial quinticBoundaryMinusTwo
    quinticBoundaryMinusOne quinticBoundaryZero quinticBoundaryOne
    quinticBoundaryTwo

theorem quintic_boundary_polynomial_coeffs :
    quinticBoundaryPolynomial =
      [{ re := 0, im := 0 }, { re := 4, im := 0 }, { re := 0, im := 0 },
        { re := -5, im := 0 }, { re := 0, im := 0 }, { re := 1, im := 0 }] := by
  native_decide

theorem quintic_boundary_eval_at_two :
    CPoly.eval quinticBoundaryPolynomial quinticBoundaryTwo = QComplex.zero := by
  native_decide

theorem quintic_boundary_deflation_chain :
    IsDeflationChain quinticBoundaryPolynomial
      [quinticBoundaryMinusTwo, quinticBoundaryMinusOne,
        quinticBoundaryZero, quinticBoundaryOne, quinticBoundaryTwo] := by
  rcases quintic_boundary_example_roots with
    ⟨hm2, hm1, hz, h1, h2⟩
  have hq1m1 := exactRoot_of_exactRoot_of_ne hm2 hm1 (by native_decide)
  have hq1z := exactRoot_of_exactRoot_of_ne hm2 hz (by native_decide)
  have hq1one := exactRoot_of_exactRoot_of_ne hm2 h1 (by native_decide)
  have hq1two := exactRoot_of_exactRoot_of_ne hm2 h2 (by native_decide)
  have hq2z := exactRoot_of_exactRoot_of_ne hq1m1 hq1z (by native_decide)
  have hq2one := exactRoot_of_exactRoot_of_ne hq1m1 hq1one (by native_decide)
  have hq2two := exactRoot_of_exactRoot_of_ne hq1m1 hq1two (by native_decide)
  have hq3one := exactRoot_of_exactRoot_of_ne hq2z hq2one (by native_decide)
  have hq3two := exactRoot_of_exactRoot_of_ne hq2z hq2two (by native_decide)
  have hq4two := exactRoot_of_exactRoot_of_ne hq3one hq3two (by native_decide)
  refine ⟨hm2, ?_⟩
  refine ⟨hq1m1, ?_⟩
  refine ⟨hq2z, ?_⟩
  refine ⟨hq3one, ?_⟩
  exact ⟨hq4two, trivial⟩

theorem quintic_boundary_deflated_coeffs :
    deflatedCoeffs quinticBoundaryPolynomial
        [quinticBoundaryMinusTwo, quinticBoundaryMinusOne,
          quinticBoundaryZero, quinticBoundaryOne, quinticBoundaryTwo] =
      [QComplex.one, QComplex.zero, QComplex.zero, QComplex.zero,
        QComplex.zero, QComplex.zero] := by
  native_decide

theorem quintic_boundary_horner_factorization (x : QComplex) :
    CPoly.eval quinticBoundaryPolynomial x =
      QComplex.mul
        (rootFactorProduct
          [quinticBoundaryMinusTwo, quinticBoundaryMinusOne,
            quinticBoundaryZero, quinticBoundaryOne, quinticBoundaryTwo] x)
        (CPoly.eval
          (deflatedCoeffs quinticBoundaryPolynomial
            [quinticBoundaryMinusTwo, quinticBoundaryMinusOne,
              quinticBoundaryZero, quinticBoundaryOne, quinticBoundaryTwo]) x) := by
  exact horner_factorization quinticBoundaryPolynomial
    [quinticBoundaryMinusTwo, quinticBoundaryMinusOne,
      quinticBoundaryZero, quinticBoundaryOne, quinticBoundaryTwo] x
    quintic_boundary_deflation_chain

theorem quintic_boundary_exact_factorization (x : QComplex) :
    CPoly.eval quinticBoundaryPolynomial x =
      rootFactorProduct
        [quinticBoundaryMinusTwo, quinticBoundaryMinusOne,
          quinticBoundaryZero, quinticBoundaryOne, quinticBoundaryTwo] x := by
  change CPoly.eval
      (factorizedQuinticPolynomial quinticBoundaryMinusTwo
        quinticBoundaryMinusOne quinticBoundaryZero quinticBoundaryOne
        quinticBoundaryTwo) x = _
  rw [factorizedQuinticPolynomial_eval_eq_product]
  simp only [rootFactorProduct]
  have hone (z : QComplex) : QComplex.mul z QComplex.one = z := by
    cases z
    simp [QComplex.mul, QComplex.one]
    grind
  rw [hone]

end ComputableAnalysis
