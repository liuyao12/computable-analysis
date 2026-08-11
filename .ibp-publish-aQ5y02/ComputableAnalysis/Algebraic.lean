import ComputableAnalysis.AlgebraicNumbers
import ComputableAnalysis.AlgebraicFunctions

/-!
# Algebraic umbrella module

The algebraic-number layer now lives in `AlgebraicNumbers.lean`.  This module
keeps older `ComputableAnalysis.Algebraic` imports working while callers move to
the more precise names.  It also collects public theorem-facing algebraic facts,
such as rational square-root irrationality criteria.
-/

namespace ComputableAnalysis

def sqrt (q : Rat)
    (h : sqrtDomain q := by unfold sqrtDomain; native_decide) : RealRaw :=
  sqrtRaw q h

def I : ComplexRaw :=
  ComplexRaw.ofQComplex RootsOfUnity.imaginaryUnitQ

/-!
## Irrationality of square roots

The sqrt algorithm and finite square criteria live in `AlgebraicFunctions.lean`;
the public irrationality statements live here with the algebraic theorem layer.
-/

/-- General theorem target for rational square roots:
if `q` is not a rational square, then the computable real produced by the
rational sqrt algorithm for `q` is irrational. -/
theorem sqrt_irrational_of_not_square
    (q : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq) :
    Rat.NotSquare q -> Real.Irrational (sqrtReal q hq h.1) := by
  intro hn r heq
  apply hn
  refine Exists.intro r ?_
  have heqRaw : (sqrtRaw q hq).Equiv (RealRaw.ofRat r) := by
    simpa [sqrtReal, Real.ofRat, Real.Equiv, Real.ofRaw] using heq
  exact sq_eq_of_sqrt_spec_equiv_rat h heqRaw

theorem sqrt_irrational_of_lowest_terms_nonsquare
    (q : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq) :
    Rat.IsNonSquareInLowestTerms q ->
      Real.Irrational (sqrtReal q hq h.1) := by
  intro hns
  exact sqrt_irrational_of_not_square q hq h
    (Rat.notSquare_of_nonSquareInLowestTerms hns)

theorem sqrt_irrational_iff_not_square
    (q : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq) :
    Real.Irrational (sqrtReal q hq h.1) ↔ Rat.NotSquare q := by
  constructor
  case mp =>
    intro hirr hsquare
    rcases hsquare with ⟨r, hr⟩
    exact hirr (qabs r) (sqrt_rational_of_square q r hq h hr)
  case mpr =>
    exact sqrt_irrational_of_not_square q hq h

/-- Lowest-terms irrationality version: `sqrt(q)` is irrational exactly when
the normalized numerator or denominator is not a square. -/
theorem sqrt_irrational_iff_lowest_terms_nonsquare
    (q : Rat) (hq : sqrtDomain q) (h : SqrtRawSpec q hq) :
    Real.Irrational (sqrtReal q hq h.1) ↔
      Rat.IsNonSquareInLowestTerms q := by
  exact Iff.trans (sqrt_irrational_iff_not_square q hq h)
    (Rat.notSquare_iff_lowest_terms_nonsquare q)

end ComputableAnalysis
