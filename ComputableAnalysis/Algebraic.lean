import ComputableAnalysis.AlgebraicNumbers
import ComputableAnalysis.AlgebraicFunctions
import ComputableAnalysis.RationalRootSearch

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
## A bounded quintic obstruction

The classical Abel--Ruffini boundary begins at degree five, but the theorem
itself is not a finite rational certificate.  The following example records
only a bounded obstruction for the monic quintic `x^5 - x + 2`: the four
integer candidates dividing its constant term are all rejected by exact
rational evaluation.  We deliberately do not promote this finite check to a
claim that the quintic has no rational root, nor to a claim about solvability
by radicals.
-/

/-- The coefficient list for the monic quintic `x^5 - x + 2`. -/
def quinticBoundaryPolynomial : List Rat := [2, -1, 0, 0, 0, 1]

/-- The finite integer candidate set used by this obstruction certificate. -/
def quinticBoundaryCandidates : List Rat := [-2, -1, 1, 2]

/-- Exact evaluations rejecting every candidate in the bounded quintic test. -/
theorem quinticBoundary_evaluation_certificate :
    Polynomial.eval quinticBoundaryPolynomial (-2) = -28 ∧
      Polynomial.eval quinticBoundaryPolynomial (-1) = 2 ∧
        Polynomial.eval quinticBoundaryPolynomial 1 = 2 ∧
          Polynomial.eval quinticBoundaryPolynomial 2 = 32 := by
  native_decide

/-- No member of the finite candidate list is a root of the quintic. -/
theorem quinticBoundary_no_candidate_root {r : Rat}
    (hr : r ∈ quinticBoundaryCandidates) :
    Polynomial.eval quinticBoundaryPolynomial r ≠ 0 := by
  simp [quinticBoundaryCandidates] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> native_decide

/-- The executable finite search rejects every supplied candidate for the
quintic boundary example.  This is a bounded rational-root certificate, not a
claim about all rational roots or about solvability by radicals. -/
theorem quinticBoundary_rationalRootSearch_none :
    RationalRootSearch.rationalRootSearch quinticBoundaryPolynomial
      quinticBoundaryCandidates = none := by
  rw [RationalRootSearch.rationalRootSearch_none_iff]
  intro r hr
  exact quinticBoundary_no_candidate_root hr

namespace RootsOfUnity

/-!
## A finite conjugate-pair closure certificate

The general root-closure question remains outside this module.  For the
explicit `X^n - 1` witness, however, a certified root and its coordinatewise
conjugate can be multiplied using only the finite `QComplex` operations.  The
following package records that particular closure without selecting a root in
a completed complex field.
-/

theorem isNthRoot_mul_conjugate {n : Nat} {z : QComplex}
    (hz : IsNthRoot n z) :
    IsNthRoot n (QComplex.mul z (conjugate z)) := by
  exact isNthRoot_mul hz (isNthRoot_conjugate hz)

/-- The norm-square of an explicitly witnessed root, packaged again with the
same finite `X^n - 1` certificate. -/
def exactRoot_mul_conjugate (n : Nat) (hn : 0 < n)
    (z : QComplex) (hz : IsNthRoot n z) : Root :=
  exactRoot_mul n hn z (conjugate z) hz (isNthRoot_conjugate hz)

end RootsOfUnity

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

theorem sqrt_thirty_six_eq_six :
    (sqrtReal (36 : Rat)
      (by unfold sqrtDomain; native_decide)
      (sqrtRaw_spec (36 : Rat)
        (by unfold sqrtDomain; native_decide)).1).Equiv
      (Real.ofRat (6 : Rat)) := by
  let hq : sqrtDomain (36 : Rat) := by
    unfold sqrtDomain
    native_decide
  have h := sqrt_rational_of_square (36 : Rat) (6 : Rat) hq
    (sqrtRaw_spec (36 : Rat) hq) (by native_decide)
  simpa [sqrtReal, qabs] using h

theorem sqrtRaw_le_am_gm {a b : Rat} (ha : 0 <= a) (hb : 0 <= b)
    (hq : sqrtDomain (a * b)) :
    (sqrtRaw (a * b) hq).Le
      (RealRaw.ofRat ((a + b) / 2)) := by
  intro n m
  change ((sqrtRaw (a * b) hq).compute n).lo <= (a + b) / 2
  have hspec := sqrtRaw_stage_spec (a * b) hq n
  have hmid : 0 <= (a + b) / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.add_nonneg ha hb)
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide)))
  exact SqrtIntervalSpec.lo_le_of_sq_le hspec hmid
    (by simpa [sq, Rat.pow_succ] using
      (am_gm_rational_half (a := a) (b := b)))

theorem sqrtRaw_am_gm_eq_of_eq {a : Rat} (ha : 0 <= a)
    (hq : sqrtDomain (a * a)) :
    (sqrtRaw (a * a) hq).Equiv
      (RealRaw.ofRat ((a + a) / 2)) := by
  have h := sqrt_rational_of_square (a * a) a hq
    (sqrtRaw_spec (a * a) hq) (by simp [sq])
  have hnot : ¬ a < 0 := by grind
  have hraw : (sqrtRaw (a * a) hq).Equiv (RealRaw.ofRat a) := by
    simpa [sqrtReal, Real.ofRat, Real.Equiv, Real.ofRaw, qabs, hnot] using h
  have hmid : (a + a) / 2 = a := by
    rw [Rat.div_def]
    have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 :=
      Rat.mul_inv_cancel 2 (by native_decide)
    grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  rw [hmid]
  exact hraw

theorem sqrtRaw_am_gm_eq_iff {a b : Rat} (ha : 0 <= a) (hb : 0 <= b)
    (hq : sqrtDomain (a * b)) :
    (sqrtRaw (a * b) hq).Equiv
        (RealRaw.ofRat ((a + b) / 2)) ↔ a = b := by
  constructor
  · intro heq
    have hsquare := sq_eq_of_sqrt_spec_equiv_rat
      (sqrtRaw_spec (a * b) hq) heq
    apply (am_gm_rational_half_eq_iff (a := a) (b := b)).mp
    simpa [sq, Rat.pow_succ] using hsquare.symm
  · intro hab
    subst b
    exact sqrtRaw_am_gm_eq_of_eq ha hq

/-- The concrete irrationality theorem used as the first algebraic benchmark. -/
theorem sqrt_two_irrational :
    Real.Irrational
      (sqrtReal (2 : Rat) (by unfold sqrtDomain; native_decide)
        (sqrtRaw_spec (2 : Rat) (by unfold sqrtDomain; native_decide)).1) := by
  let hq : sqrtDomain (2 : Rat) := by
    unfold sqrtDomain
    native_decide
  have hnon : Rat.IsNonSquareInLowestTerms (2 : Rat) := by
    unfold Rat.IsNonSquareInLowestTerms
    left
    intro hsquare
    rcases hsquare with ⟨_, ⟨k, hk⟩⟩
    have hkabs : (Rat.num (2 : Rat)).natAbs = 2 := by native_decide
    rw [hkabs] at hk
    by_cases hsmall : k < 2
    · have hkcases : k = 0 ∨ k = 1 := by omega
      cases hkcases with
      | inl hk0 => subst k; omega
      | inr hk1 => subst k; omega
    · have hlarge : 2 ≤ k := Nat.le_of_not_gt hsmall
      have hbound := Nat.mul_self_le_mul_self hlarge
      omega
  exact sqrt_irrational_of_lowest_terms_nonsquare
    (2 : Rat) hq (sqrtRaw_spec 2 hq) hnon

end ComputableAnalysis
