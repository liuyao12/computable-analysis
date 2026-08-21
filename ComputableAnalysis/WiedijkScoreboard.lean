import ComputableAnalysis.IrrationalSqrt
import ComputableAnalysis.SqrtTwoDescent
import ComputableAnalysis.Polynomial
import ComputableAnalysis.RationalCircle
import ComputableAnalysis.FiniteBinomialCertificate
import ComputableAnalysis.EffectiveFTCPortfolio
import ComputableAnalysis.FirstYearCalculus
import ComputableAnalysis.FiniteDeMoivreExample
import ComputableAnalysis.FiniteCubeRootBisectionExample
import ComputableAnalysis.FinitePrimeInfinitude
import ComputableAnalysis.FiniteBertrandCertificate
import ComputableAnalysis.CubicRootWitnessCertificate
import ComputableAnalysis.FiniteGreenRectangle
import ComputableAnalysis.FiniteIsoperimetricCertificate
import ComputableAnalysis.FiniteGeometryFormulaInterfaces
import ComputableAnalysis.FiniteCayleyHamiltonExample
import ComputableAnalysis.FiniteChordPowerExample
import ComputableAnalysis.FiniteTriangleIsoperimetricCertificate
import ComputableAnalysis.FinitePellCertificate
import ComputableAnalysis.FiniteQuarticSplitExample
import ComputableAnalysis.FiniteHarmonicGrowthInterface
import ComputableAnalysis.FiniteInverseSearchInterface
import ComputableAnalysis.PolynomialMeanValue
import ComputableAnalysis.FiniteQuadratureMeanValue
import ComputableAnalysis.FiniteMonotoneSequenceInterface
import ComputableAnalysis.FiniteLHopitalCertificate
import ComputableAnalysis.Basel
import ComputableAnalysis.BaselFiniteStrengthening
import ComputableAnalysis.FiniteFourierCertificate
import ComputableAnalysis.FiniteFourierFoundation
import ComputableAnalysis.EffectiveFourierSeries
import ComputableAnalysis.EffectiveFourierTail
import ComputableAnalysis.FiniteFourierGeometric
import ComputableAnalysis.FiniteCauchySchwarzList
import ComputableAnalysis.FiniteComplexQuadraticExample
import ComputableAnalysis.FiniteDigitDivisibilityInterface
import ComputableAnalysis.FinitePickCertificate
import ComputableAnalysis.FinitePickInterface
import ComputableAnalysis.FiniteInductionExample
import ComputableAnalysis.FiniteLawOfCosinesExample
import ComputableAnalysis.FinitePtolemyLength
import ComputableAnalysis.FiniteCramerExample
import ComputableAnalysis.FiniteDescartesExamples
import ComputableAnalysis.FiniteDescartesInterface
import ComputableAnalysis.FinitePrimeFactorExample
import ComputableAnalysis.CauchyPi
import ComputableAnalysis.FinitePrimeReciprocalCertificate
import ComputableAnalysis.FiniteStirlingInterface
import ComputableAnalysis.BaselFiniteComparison

/-!
# Wiedijk's List scoreboard

This is the machine-readable companion to the 52 scoped rows in the
blueprint.  A row records the benchmark number and the project-facing name;
the theorem itself is proved in its subject module.  The list is deliberately
not a claim that every unrestricted classical statement has been reproduced:
each row is the computable or certificate-level target selected by the
blueprint.
-/

namespace ComputableAnalysis

structure WiedijkEntry where
  number : Nat
  name : String
deriving Repr, DecidableEq

def wiedijkScopedEntries : List WiedijkEntry := [
  ⟨1, "Irrationality of sqrt 2"⟩,
  ⟨2, "Fundamental theorem of algebra"⟩,
  ⟨3, "Denumerability of the rationals"⟩,
  ⟨4, "Pythagorean theorem"⟩,
  ⟨8, "Doubling the cube"⟩,
  ⟨9, "Area of a circle"⟩,
  ⟨11, "Infinitude of primes"⟩,
  ⟨14, "Basel sum"⟩,
  ⟨15, "Fundamental theorem of integral calculus"⟩,
  ⟨16, "Abel--Ruffini boundary"⟩,
  ⟨17, "de Moivre formula"⟩,
  ⟨21, "Green theorem"⟩,
  ⟨23, "Pythagorean triples"⟩,
  ⟨26, "Leibniz series for pi"⟩,
  ⟨27, "Sum of angles of a triangle"⟩,
  ⟨34, "Divergence of the harmonic series"⟩,
  ⟨35, "Taylor theorem"⟩,
  ⟨37, "Solution of a cubic"⟩,
  ⟨39, "Pell equation"⟩,
  ⟨43, "Isoperimetric theorem"⟩,
  ⟨44, "Binomial theorem"⟩,
  ⟨46, "General quartic equation"⟩,
  ⟨49, "Cayley--Hamilton theorem"⟩,
  ⟨55, "Product of chord segments"⟩,
  ⟨57, "Heron's formula"⟩,
  ⟨60, "Bezout identity"⟩,
  ⟨64, "L'Hopital rule"⟩,
  ⟨65, "Isosceles triangle theorem"⟩,
  ⟨66, "Geometric series"⟩,
  ⟨68, "Arithmetic series"⟩,
  ⟨69, "Greatest common divisor"⟩,
  ⟨73, "Monotone sequences"⟩,
  ⟨74, "Mathematical induction"⟩,
  ⟨75, "Mean value theorem"⟩,
  ⟨76, "Fourier series"⟩,
  ⟨79, "Intermediate value theorem"⟩,
  ⟨80, "Fundamental theorem of arithmetic"⟩,
  ⟨81, "Prime reciprocal series"⟩,
  ⟨89, "Factor and remainder theorems"⟩,
  ⟨91, "Triangle inequality"⟩,
  ⟨92, "Pick theorem"⟩,
  ⟨94, "Law of cosines"⟩,
  ⟨95, "Ptolemy theorem"⟩,
  ⟨97, "Cramer's rule"⟩,
  ⟨98, "Bertrand postulate"⟩,
  ⟨100, "Descartes rule of signs"⟩,
  ⟨38, "Arithmetic--geometric mean inequality"⟩,
  ⟨42, "Reciprocal triangular numbers"⟩,
  ⟨77, "Sums of powers"⟩,
  ⟨78, "Cauchy--Schwarz inequality"⟩,
  ⟨85, "Divisibility by 3"⟩,
  ⟨90, "Stirling formula"⟩
]

/-! The smaller track used to measure progress toward the project's actual
computable calculus.  The remaining rows are useful formalization
infrastructure, but are not evidence that the calculus foundation is done. -/
def wiedijkCalculusAnalysisEntries : List WiedijkEntry := [
  ⟨9, "Area of a circle"⟩,
  ⟨14, "Basel sum"⟩,
  ⟨15, "Fundamental theorem of integral calculus"⟩,
  ⟨21, "Green theorem"⟩,
  ⟨26, "Leibniz series for pi"⟩,
  ⟨35, "Taylor theorem"⟩,
  ⟨43, "Isoperimetric theorem"⟩,
  ⟨64, "L'Hopital rule"⟩,
  ⟨66, "Geometric series"⟩,
  ⟨73, "Monotone sequences"⟩,
  ⟨75, "Mean value theorem"⟩,
  ⟨76, "Fourier series"⟩,
  ⟨77, "Sums of powers"⟩,
  ⟨78, "Cauchy--Schwarz inequality"⟩,
  ⟨79, "Intermediate value theorem"⟩,
  ⟨81, "Prime reciprocal series"⟩,
  ⟨90, "Stirling formula"⟩
]

theorem wiedijkScopedEntries_count : wiedijkScopedEntries.length = 52 := by
  native_decide

theorem wiedijkCalculusAnalysisEntries_count :
    wiedijkCalculusAnalysisEntries.length = 17 := by
  native_decide

def wiedijkCalculusAnalysisAnchoredEntries : List WiedijkEntry := [
  ⟨9, "Certified circle-area computation"⟩,
  ⟨15, "Effective fundamental theorem of integral calculus"⟩,
  ⟨21, "Finite Green rectangle certificate"⟩,
  ⟨26, "Certified Leibniz series"⟩,
  ⟨35, "Certified Taylor table"⟩,
  ⟨43, "Finite isoperimetric bound"⟩,
  ⟨64, "Finite L'Hopital residual certificate"⟩,
  ⟨66, "Finite geometric series"⟩,
  ⟨73, "Finite monotone-sequence order"⟩,
  ⟨75, "Effective mean-value enclosure"⟩,
  ⟨77, "Finite sum-of-squares identity"⟩,
  ⟨78, "Rational Cauchy--Schwarz"⟩,
  ⟨79, "Finite intermediate-value bracket"⟩,
  ⟨81, "Finite prime-reciprocal extension"⟩,
  ⟨76, "Effective Fourier finite-stage and tail certificate"⟩,
  ⟨90, "Finite Stirling-ratio certificate"⟩
]

theorem wiedijkCalculusAnalysisAnchoredEntries_count :
    wiedijkCalculusAnalysisAnchoredEntries.length = 16 := by
  native_decide

/-! The difference between the calculus/analysis proxy and the anchored
track is deliberately explicit.  Basel remains a target statement about the
equivalence of two independently valid raw algorithms; its finite overlap and
effective-series substitute are tracked below, but do not close the identity. -/
def wiedijkCalculusAnalysisUnresolvedEntries : List WiedijkEntry := [
  ⟨14, "Basel identity: zeta(2) = pi^2 / 6"⟩
]

theorem wiedijkCalculusAnalysisUnresolvedEntries_count :
    wiedijkCalculusAnalysisUnresolvedEntries.length = 1 := by
  native_decide

/-! Finite evidence for rows whose unrestricted analytic statement is still
open.  These certificates are tracked separately from the anchored theorem
count because a few checked stages do not establish an all-stage equivalence. -/
def wiedijkCalculusAnalysisFiniteEvidenceEntries : List WiedijkEntry := [
  ⟨14, "Finite Basel interval overlap"⟩
]

theorem wiedijkCalculusAnalysisFiniteEvidenceEntries_count :
    wiedijkCalculusAnalysisFiniteEvidenceEntries.length = 1 := by
  native_decide

def wiedijkCalculusAnalysisComputableSubstitutes : List WiedijkEntry := [
  ⟨14, "Effective Basel-series convergence"⟩
]

theorem wiedijkCalculusAnalysisComputableSubstitutes_count :
    wiedijkCalculusAnalysisComputableSubstitutes.length = 1 := by
  native_decide

/-! First completed row: the benchmark statement is exposed directly through
the project's raw-real irrationality predicate, rather than Mathlib's
completed real-number predicate. -/
theorem wiedijk_item_one_sqrt_two :
    RealRaw.Irrational (sqrtRat (2 : Rat) (by native_decide)) := by
  exact sqrt_two_irrational_via_descent

/-! Item 2 in its constructive finite boundary: a complex quadratic with
exact rational-coordinate roots and an executable factorization certificate.
This records the computable replacement, not unrestricted root existence for
all complex polynomials. -/
theorem wiedijk_item_two_finite_complex_quadratic_certificate :
    CPoly.eval finiteComplexQuadratic finiteComplexQuadraticUpper =
        QComplex.zero /\
      CPoly.eval finiteComplexQuadratic finiteComplexQuadraticLower =
        QComplex.zero /\
      finiteComplexQuadraticUpper ≠ finiteComplexQuadraticLower /\
      (forall z : QComplex,
        CPoly.eval finiteComplexQuadratic z =
          QComplex.mul
            (QComplex.sub z finiteComplexQuadraticUpper)
            (QComplex.sub z finiteComplexQuadraticLower)) := by
  exact ⟨finiteComplexQuadratic_upper_root,
    finiteComplexQuadratic_lower_root,
    finiteComplexQuadratic_roots_distinct,
    finiteComplexQuadratic_factorization⟩

/-! The worked polynomial is an instance of the reusable factorized quadratic
interface.  This is the computable FTA boundary: supplied exact complex roots
give an executable polynomial and an exact root characterization. -/
theorem wiedijk_item_two_factorized_quadratic_root_characterization
    (r s z : QComplex) :
    CPoly.hasExactRoot
        (factorizedQuadraticPolynomial r s) z ↔ z = r ∨ z = s := by
  exact factorizedQuadraticPolynomial_hasExactRoot_iff r s z

/-! Item 16 in its constructive finite boundary: a bounded rational-root
search for a monic quintic returns no candidate.  This does not assert the
classical impossibility theorem or provide a general radicals solver. -/
theorem wiedijk_item_sixteen_finite_quintic_rational_root_boundary :
    RationalRootSearch.rationalRootSearch
        quinticBoundaryPolynomial quinticBoundaryCandidates = none := by
  exact quinticBoundary_rationalRootSearch_none

/-! The finite Abel--Ruffini boundary uses the general exact candidate search:
failure means precisely that no supplied exact candidate is a root. -/
theorem wiedijk_item_sixteen_exact_candidate_search_none_iff
    {coeffs : CPoly.Coeffs} {candidates : List QComplex} :
    exactRootSearch coeffs candidates = none ↔
      ∀ z, z ∈ candidates -> ¬ CPoly.hasExactRoot coeffs z := by
  exact exactRootSearch_none_iff

theorem wiedijk_item_sixteen_factorized_quintic_root_characterization
    (r₁ r₂ r₃ r₄ r₅ z : QComplex) :
    CPoly.hasExactRoot
        (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅) z ↔
      z ∈ [r₁, r₂, r₃, r₄, r₅] := by
  exact factorizedQuinticPolynomial_hasExactRoot_iff_mem
    r₁ r₂ r₃ r₄ r₅ z

theorem wiedijk_item_three_denumerability (q : Rat) :
    Exists fun n : Nat => RationalCode.decode (rationalNatCode n) = q := by
  exact rationalNatCode_decode_surjective q

theorem wiedijk_item_three_canonical_code (q : Rat) :
    rationalNatCode (rationalNatIndex q) = RationalCode.encode q := by
  exact rationalNatCode_index q

theorem wiedijk_item_three_canonical_index_unique (q : Rat) :
    ∃ n : Nat, rationalNatCode n = RationalCode.encode q ∧
      ∀ m : Nat, rationalNatCode m = RationalCode.encode q -> m = n := by
  obtain ⟨n, hn, huniq⟩ := rationalNatCode_existsUnique_canonical_index q
  exact ⟨n, hn, huniq⟩

theorem wiedijk_item_three_canonical_decode_index_unique (q : Rat) :
    ∃ n : Nat,
      (rationalNatCode n = RationalCode.encode q ∧
        RationalCode.decode (rationalNatCode n) = q) ∧
      ∀ m : Nat,
        (rationalNatCode m = RationalCode.encode q ∧
          RationalCode.decode (rationalNatCode m) = q) -> m = n := by
  obtain ⟨n, hn, huniq⟩ :=
    rationalNatCode_existsUnique_canonical_decode_index q
  exact ⟨n, hn, huniq⟩

theorem wiedijk_item_four_pythagorean
    (u v : PiCirclePoint) (horth : RationalCircle.Stage.dot u v = 0) :
    RationalCircle.Stage.segmentNormSq RationalCircle.Stage.origin u +
        RationalCircle.Stage.segmentNormSq RationalCircle.Stage.origin v =
      RationalCircle.Stage.segmentNormSq u v := by
  exact RationalCircle.Stage.rightTriangle_pythagorean u v horth

/-! Item 27 in its rational-coordinate boundary: the oriented triangle
determinant has the cyclic and orientation-reversal laws underlying the
classical angle-sum argument.  No completed angle values are introduced. -/
theorem wiedijk_item_twenty_seven_oriented_triangle_boundary
    (p q r : PiCirclePoint) :
    RationalCircle.triangleTwiceArea p q r =
        RationalCircle.triangleTwiceArea q r p /\
      RationalCircle.triangleTwiceArea p q r =
        -RationalCircle.triangleTwiceArea p r q := by
  exact ⟨RationalCircle.triangleTwiceArea_cyclic p q r,
    RationalCircle.triangleTwiceArea_swap_neg p q r⟩

theorem wiedijk_item_twenty_seven_triangle_shoelace
    (p q r : PiCirclePoint) :
    RationalCircle.triangleTwiceArea p q r =
      p.x * q.y + q.x * r.y + r.x * p.y -
        (p.y * q.x + q.y * r.x + r.y * p.x) := by
  exact RationalCircle.triangleTwiceArea_shoelace p q r

theorem wiedijk_item_twenty_seven_quadrilateral_area_additivity
    (p q r s : PiCirclePoint) :
    RationalCircle.triangleTwiceArea p q r +
        RationalCircle.triangleTwiceArea p r s =
      RationalCircle.triangleTwiceArea p q s +
        RationalCircle.triangleTwiceArea q r s := by
  exact RationalCircle.triangleTwiceArea_quadrilateral_diagonal_additivity p q r s

/-! Item 85 in its terminating computable form: divisibility by three is
decided by the decimal digit sum, with the residue equality exposed. -/
theorem wiedijk_item_eighty_five_decimal_divisibility (n : Nat) :
    (3 ∣ n ↔ 3 ∣ decimalDigitSum n) /\
      decimalDigitSum n % 3 = n % 3 := by
  exact decimalDigitSum_divisibility_certificate n

theorem wiedijk_item_eighty_five_decimal_digit_sum_mod_nine (n : Nat) :
    decimalDigitSum n % 9 = n % 9 := by
  exact decimalDigitSum_mod_nine n

/-! Item 89 in its finite complex form: for a supplied factor list, the
Horner evaluator vanishes exactly at the listed roots. -/
theorem wiedijk_item_eighty_nine_factor_remainder_boundary
  (roots : List QComplex) (z : QComplex) :
    CPoly.eval (factorizedPolynomial roots) z = QComplex.zero ↔
      z ∈ roots := by
  exact factorizedPolynomial_eval_eq_zero_iff_mem

theorem wiedijk_item_eighty_nine_generic_remainder_formula
    {coeffs : List Rat} {r x : Rat}
    (certificate : Polynomial.RemainderCertificate coeffs r) :
    Polynomial.eval coeffs x = certificate.remainder +
      (x - r) * Polynomial.eval certificate.quotient x := by
  exact certificate.factor_remainder_at

theorem wiedijk_item_eighty_nine_generic_factor_theorem
    {coeffs : List Rat} {r x : Rat}
    (certificate : Polynomial.RemainderCertificate coeffs r)
    (hroot : Polynomial.eval coeffs r = 0) :
    Polynomial.eval coeffs x =
      (x - r) * Polynomial.eval certificate.quotient x := by
  exact certificate.factor_of_root hroot

theorem wiedijk_item_eighty_nine_remainder_root_iff
    {coeffs : List Rat} {r : Rat}
    (certificate : Polynomial.RemainderCertificate coeffs r) :
    certificate.remainder = 0 ↔ Polynomial.eval coeffs r = 0 := by
  exact certificate.remainder_eq_zero_iff

/-! Item 92 in its finite lattice boundary: several exact triangles satisfy
Pick's area identity using shoelace area, gcd edge counts, and natural-number
interior counts. -/
theorem wiedijk_item_ninety_two_finite_pick_certificates :
    (pickTriangleArea = 6 /\
      pickTriangleBoundary = 8 /\
      pickTriangleInterior = 3 /\
      pickTriangleArea = (pickTriangleInterior : Rat) +
        (pickTriangleBoundary : Rat) / 2 - 1) /\
    (pickTriangleTwoArea = 5 /\
      pickTriangleTwoBoundary = 8 /\
      pickTriangleTwoInterior = 2 /\
      pickTriangleTwoArea = (pickTriangleTwoInterior : Rat) +
        (pickTriangleTwoBoundary : Rat) / 2 - 1) /\
    (pickTriangleThreeArea = 15 / 2 /\
      pickTriangleThreeBoundary = 5 /\
      pickTriangleThreeInterior = 6 /\
      pickTriangleThreeArea = (pickTriangleThreeInterior : Rat) +
        (pickTriangleThreeBoundary : Rat) / 2 - 1) /\
    (pickTriangleFourArea = 15 /\
      pickTriangleFourBoundary = 8 /\
      pickTriangleFourInterior = 12 /\
      pickTriangleFourArea = (pickTriangleFourInterior : Rat) +
        (pickTriangleFourBoundary : Rat) / 2 - 1) := by
  exact ⟨pickTriangle_certificate, pickTriangleTwo_certificate,
    pickTriangleThree_certificate, pickTriangleFour_certificate⟩

theorem wiedijk_item_ninety_two_generic_pick_identity
    (certificate : FinitePickTriangleCertificate) :
    certificate.area = (certificate.interior : Rat) +
      (certificate.boundary : Rat) / 2 - 1 := by
  exact certificate.identity

theorem wiedijk_item_ninety_two_generic_pick_data
    (certificate : FinitePickTriangleCertificate) :
    certificate.area =
        qabs (RationalCircle.triangleTwiceArea
          certificate.vertexA.toRat certificate.vertexB.toRat
          certificate.vertexC.toRat) / 2 /\
      certificate.boundary =
        Nat.gcd (Int.natAbs (certificate.vertexB.x - certificate.vertexA.x))
            (Int.natAbs (certificate.vertexB.y - certificate.vertexA.y)) +
          Nat.gcd (Int.natAbs (certificate.vertexC.x - certificate.vertexB.x))
            (Int.natAbs (certificate.vertexC.y - certificate.vertexB.y)) +
          Nat.gcd (Int.natAbs (certificate.vertexA.x - certificate.vertexC.x))
            (Int.natAbs (certificate.vertexA.y - certificate.vertexC.y)) := by
  exact ⟨certificate.area_eq, certificate.boundary_eq⟩

/-! The remaining algebraic rows are exposed at their finite certificate
boundary.  These statements deliberately retain the exact rational data and
do not silently promote them to a completed Euclidean or real-number theorem. -/

theorem wiedijk_item_seventy_four_induction_certificate (n : Nat) :
    Series.arithmeticSum n = (n : Rat) * ((n : Rat) - 1) / 2 := by
  exact induction_arithmeticSum_eq n

theorem wiedijk_item_eighty_finite_prime_factor_certificate :
    primeFactorizationCertificate360.factors.foldl (fun acc p => acc * p) 1 = 360 /\
      primeFactorizationCertificate360_alternative.factors.foldl (fun acc p => acc * p) 1 = 360 /\
      primeFactorizationCertificate360.factors.Perm
        primeFactorizationCertificate360_alternative.factors := by
  exact ⟨primeFactorizationCertificate360_product,
    by native_decide, primeFactorizationCertificate360_factor_order_unique⟩

theorem wiedijk_item_eighty_finite_unique_factorization
    {n : Nat} (c₁ c₂ : PrimeFactorCertificate n) :
    c₁.factors.Perm c₂.factors := by
  exact PrimeFactorCertificate.factor_perm c₁ c₂

theorem wiedijk_item_ninety_four_law_of_cosines_certificate :
    let p : PiCirclePoint := { x := 3 / 5, y := 4 / 5 }
    let q : PiCirclePoint := { x := -4 / 5, y := 3 / 5 }
    RationalCircle.Stage.normSq p = 1 /\
      RationalCircle.Stage.normSq q = 1 /\
      RationalCircle.Stage.dot p q = 0 /\
      RationalCircle.Stage.segmentNormSq p q = 2 /\
      RationalCircle.Stage.segmentNormSq p q =
        RationalCircle.Stage.normSq p + RationalCircle.Stage.normSq q -
          2 * RationalCircle.Stage.dot p q := by
  exact RationalCircle.Stage.finiteLawOfCosines_unit_orthogonal_certificate

theorem wiedijk_item_ninety_four_law_of_cosines_general
    (p q : PiCirclePoint) :
    RationalCircle.Stage.segmentNormSq p q =
      RationalCircle.Stage.normSq p + RationalCircle.Stage.normSq q -
        2 * RationalCircle.Stage.dot p q := by
  exact RationalCircle.Stage.segmentNormSq_law_of_cosines p q

theorem wiedijk_item_ninety_five_ptolemy_certificate :
    (PtolemyLengthCore.pointSegmentLengthRaw
        FinitePtolemyLength.ptolemyPointA FinitePtolemyLength.ptolemyPointB).Equiv
        (RealRaw.ofRat (16 / 17)) /\
      (16 / 17 : Rat) * (14 / 25) + (26 / 85) * (8 / 5) =
        (6 / 5) * (72 / 85) := by
  exact ⟨FinitePtolemyLength.finitePtolemyLength_certificate.1,
    FinitePtolemyLength.finitePtolemyLength_certificate.2.2.2.2.2.2⟩

theorem wiedijk_item_ninety_five_oriented_chord_numerator
    (a b c d : Rat) :
    (c - a) * (d - b) =
      (b - a) * (d - c) + (c - b) * (d - a) := by
  exact RationalCircle.ptolemy_oriented_chord_numerator a b c d

theorem wiedijk_item_ninety_seven_cramer_certificate :
    (2 : Rat) * 3 - 1 * 1 = 5 /\
      (5 * 3 - 1 * 10) / (2 * 3 - 1 * 1) = 1 /\
      (2 * 10 - 5 * 1) / (2 * 3 - 1 * 1) = 3 /\
      ((2 : Rat) * 1 + 1 * 3 = 5 /\ 1 * 1 + 3 * 3 = 10) := by
  exact cramer_2_1_1_3_certificate

theorem wiedijk_item_ninety_seven_rational_two_by_two_cramer
    (a b c d x y : Rat) (hdet : a * d - b * c ≠ 0) :
    a * ((x * d - b * y) / (a * d - b * c)) +
          b * ((a * y - x * c) / (a * d - b * c)) = x /\
      c * ((x * d - b * y) / (a * d - b * c)) +
          d * ((a * y - x * c) / (a * d - b * c)) = y := by
  have hcancel : (a * d - b * c)⁻¹ * (a * d - b * c) = 1 :=
    Rat.inv_mul_cancel _ hdet
  constructor <;> rw [Rat.div_def, Rat.div_def]
  · grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  · grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem wiedijk_item_twenty_one_green_rectangle_additivity
    (left middle right bottom top : Rat) :
    greenRectangleBoundary left middle bottom top +
        greenRectangleBoundary middle right bottom top =
      greenRectangleBoundary left right bottom top /\
    greenRectangleArea left middle bottom top +
        greenRectangleArea middle right bottom top =
      greenRectangleArea left right bottom top := by
  exact ⟨greenRectangleBoundary_split_horizontal left middle right bottom top,
    greenRectangleArea_split_horizontal left middle right bottom top⟩

theorem wiedijk_item_twenty_one_green_rectangle_boundary_area
    (left right bottom top : Rat) :
    greenRectangleBoundary left right bottom top =
      greenRectangleArea left right bottom top := by
  exact greenRectangleBoundary_eq_area left right bottom top

theorem wiedijk_item_twenty_one_green_rectangle_vertical_additivity
    (left right bottom middle top : Rat) :
    greenRectangleBoundary left right bottom middle +
        greenRectangleBoundary left right middle top =
      greenRectangleBoundary left right bottom top /\
    greenRectangleArea left right bottom middle +
        greenRectangleArea left right middle top =
      greenRectangleArea left right bottom top := by
  exact ⟨greenRectangleBoundary_split_vertical left right bottom middle top,
    greenRectangleArea_split_vertical left right bottom middle top⟩

theorem wiedijk_item_one_hundred_descartes_certificate :
    Polynomial.signChangeCountIgnoringZeros Polynomial.twoVariationQuadratic = 2 /\
      (forall x : Rat, 0 < x ->
        (Polynomial.eval Polynomial.twoVariationQuadratic x = 0 ↔
          x = 1 ∨ x = 2)) := by
  exact Polynomial.twoVariationQuadratic_certificate

theorem wiedijk_item_one_hundred_finite_descartes_bound
    (certificate : Polynomial.FiniteDescartesSignCertificate) :
    Polynomial.signChangeCountIgnoringZeros certificate.coefficients =
        certificate.variationCount /\
      certificate.variationCount + 1 <= certificate.filteredLength := by
  exact ⟨certificate.variation_eq_count,
    certificate.variation_bound⟩

theorem wiedijk_item_one_hundred_direct_descartes_variation_bound
    {coefficients : List Rat}
    (hne : (coefficients.filter (fun c => c != 0)).length > 0) :
    Polynomial.signChangeCountIgnoringZeros coefficients + 1 <=
      (coefficients.filter (fun c => c != 0)).length := by
  exact Polynomial.signChangeCountIgnoringZeros_add_one_le_filter_length hne

theorem wiedijk_item_forty_four_binomial_certificate :
    Series.binomialSum 5 2 1 6 = 243 := by
  exact binomial_stage5_two_one_value

/-! The benchmark example is backed by the reusable finite binomial law.  The
sum is indexed only through `n + 1`, so this is an exact rational computation
with no appeal to an infinite expansion. -/
theorem wiedijk_item_forty_four_binomial_theorem
    (n : Nat) (x y : Rat) :
    Series.binomialSum n x y (n + 1) = (x + y) ^ n := by
  exact Series.binomialSum_eq_pow n x y

theorem wiedijk_item_forty_four_binomial_pascal_row
    {n k : Nat} (hk : k <= n) (x y : Rat) :
    Series.binomialSum (n + 1) x y (k + 1) =
      x * Series.binomialSum n x y (k + 1) +
        y * Series.binomialSum n x y k := by
  exact Series.binomialSum_succ_row hk x y

theorem wiedijk_item_forty_four_binomial_stabilization
    {n count : Nat} (hcount : n + 1 <= count) (x y : Rat) :
    Series.binomialSum n x y count = (x + y) ^ n := by
  exact Series.binomialSum_eq_pow_of_reached hcount x y

theorem wiedijk_item_sixty_bezout (a b : Nat) :
    Exists fun x : Int =>
      Exists fun y : Int =>
        x * (a : Int) + y * (b : Int) = (Nat.gcd a b : Int) := by
  exact bezout_exists a b

theorem wiedijk_item_sixty_euclidean_bezout (a b : Nat) :
    Exists fun x : Int =>
      Exists fun y : Int =>
        x * (a : Int) + y * (b : Int) = (euclideanGcd a b : Int) := by
  exact euclideanGcd_bezout_exists a b

theorem wiedijk_item_sixty_nine_gcd (a b : Nat) :
    euclideanGcd a b = Nat.gcd a b := by
  exact euclideanGcd_eq_gcd a b

theorem wiedijk_item_sixty_nine_gcd_divisibility
    {a b d : Nat} :
    d ∣ euclideanGcd a b ↔ d ∣ a ∧ d ∣ b := by
  exact euclideanGcd_dvd_iff

theorem wiedijk_item_sixty_six_geometric_series
    (r : Rat) (hr : r ≠ 1) (n : Nat) :
    Series.geometricSum r n = (r ^ n - 1) / (r - 1) := by
  exact Series.geometricSum_eq r hr n

theorem wiedijk_item_sixty_six_geometric_tail_identity
    (r : Rat) (n : Nat) :
    1 - (1 - r) * Series.geometricSum r n = r ^ n := by
  exact Series.geometricSum_tail_eq r n

theorem wiedijk_item_sixty_six_geometric_tail_bound
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (n : Nat) :
    1 - (1 - r) * Series.geometricSum r n <=
      1 / ((n + 1 : Nat) : Rat) := by
  exact Series.geometricSum_tail_le_one_div_succ_of_le_half
    hr0 hrhalf n

theorem wiedijk_item_sixty_six_geometric_raw_valid
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) :
    (Series.geometricRaw r hr0 hr1).Valid := by
  exact Series.geometricRaw_valid_of_le_half hr0 hrhalf hr1

theorem wiedijk_item_sixty_six_geometric_raw_closed_form
    {r : Rat} (hr0 : 0 <= r) (hr1 : r < 1) :
    (Series.geometricRaw r hr0 hr1).Equiv
      (RealRaw.ofRat (1 / (1 - r))) := by
  exact Series.geometricRaw_equiv_inv_one_sub hr0 hr1

theorem wiedijk_item_sixty_six_geometric_raw_precision
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) (eps : QPos) :
    ∃ n : Nat, ((Series.geometricRaw r hr0 hr1).compute n).width <= eps.val := by
  exact Series.geometricRaw_reaches_of_positive_tolerance
    hr0 hrhalf hr1 eps

theorem wiedijk_item_sixty_eight_arithmetic_series (n : Nat) :
    Series.arithmeticSum n = (n : Rat) * ((n : Rat) - 1) / 2 := by
  exact Series.arithmeticSum_eq n

theorem wiedijk_item_sixty_eight_arithmetic_progression_sum
    (a d : Rat) (n : Nat) :
    Series.arithmeticProgressionSum a d n =
      (n : Rat) * (2 * a + ((n : Rat) - 1) * d) / 2 := by
  exact Series.arithmeticProgressionSum_eq a d n

theorem wiedijk_item_sixty_eight_arithmetic_progression_monotone
    {a d : Rat} (ha : 0 <= a) (hd : 0 <= d)
    {n m : Nat} (hnm : n <= m) :
    Series.arithmeticProgressionSum a d n <=
      Series.arithmeticProgressionSum a d m := by
  exact Series.arithmeticProgressionSum_le_of_le ha hd hnm

theorem wiedijk_item_seventy_seven_sum_of_squares (n : Nat) :
    Series.squareSum n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) / 6 := by
  exact Series.squareSum_eq n

/-! The square formula is a checked instance of the more general finite
power-sum interface.  Its recurrence and block law are the computable core
of sums of powers; no infinite series or completed real is involved. -/
theorem wiedijk_item_seventy_seven_generic_power_sum_step
    (k n : Nat) :
    Series.powerSum k (n + 1) =
      Series.powerSum k n + (n : Rat) ^ k := by
  exact Series.powerSum_succ k n

theorem wiedijk_item_seventy_seven_generic_power_sum_block
    (k n m : Nat) :
    Series.powerSum k (n + m) =
      Series.powerSum k n + Series.powerSumBlock k n m := by
  exact Series.powerSum_add_block k n m

theorem wiedijk_item_seventy_seven_cube_sum_closed_form (n : Nat) :
    Series.powerSum 3 n =
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 / 4 := by
  exact Series.powerSum_three_closed_form n

theorem wiedijk_item_seventy_seven_fourth_power_sum_closed_form (n : Nat) :
    Series.powerSum 4 n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (3 * (n : Rat) ^ 2 - 3 * (n : Rat) - 1) / 30 := by
  exact Series.powerSum_four_closed_form n

theorem wiedijk_item_seventy_seven_fifth_power_sum_closed_form (n : Nat) :
    Series.powerSum 5 n =
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 *
        (2 * (n : Rat) ^ 2 - 2 * (n : Rat) - 1) / 12 := by
  exact Series.powerSum_five_closed_form n

theorem wiedijk_item_seventy_seven_sixth_power_sum_closed_form (n : Nat) :
    Series.powerSum 6 n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (3 * (n : Rat) ^ 4 - 6 * (n : Rat) ^ 3 + 3 * (n : Rat) + 1) / 42 := by
  exact Series.powerSum_six_closed_form n

theorem wiedijk_item_seventy_seven_seventh_power_sum_closed_form (n : Nat) :
    Series.powerSum 7 n =
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 *
        (3 * (n : Rat) ^ 4 - 6 * (n : Rat) ^ 3 - (n : Rat) ^ 2 +
          4 * (n : Rat) + 2) / 24 := by
  exact Series.powerSum_seven_closed_form n

theorem wiedijk_item_seventy_seven_eighth_power_sum_closed_form (n : Nat) :
    Series.powerSum 8 n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (5 * (n : Rat) ^ 6 - 15 * (n : Rat) ^ 5 +
          5 * (n : Rat) ^ 4 + 15 * (n : Rat) ^ 3 -
          (n : Rat) ^ 2 - 9 * (n : Rat) - 3) / 90 := by
  exact Series.powerSum_eight_closed_form n

/-! Item 15 is represented here by the project's effective, certificate-level
FTC portfolio.  This is deliberately a bundle of proved instances rather
than the unrestricted classical theorem for every continuous function. -/
theorem wiedijk_item_fifteen_effective_ftc : EffectiveFTCPortfolio := by
  exact effectiveFTCPortfolio

/-! The reusable FTC theorem is exposed separately from the portfolio of
concrete examples.  Its hypotheses are finite derivative-bound certificates;
the conclusion is equivalence of the bounded Riemann-style integral and the
endpoint difference as raw computable reals. -/
theorem wiedijk_item_fifteen_derivative_bound_ftc
    {F dF : RealFunRaw} {a b : Rat}
    (certificate : DerivativeBoundFTC F dF a b) :
    certificate.boundedIntegralRaw.Equiv certificate.endpointRaw := by
  exact certificate.equiv_endpoint

theorem wiedijk_item_fifteen_derivative_bound_ftc_close_at
    {F dF : RealFunRaw} {a b : Rat}
    (certificate : DerivativeBoundFTC F dF a b) (eps : QPos) :
    QInterval.CloseAt
      (certificate.boundedIntegralInterval eps)
      (certificate.endpointInterval eps) eps := by
  exact certificate.closeAt eps

theorem wiedijk_item_fifteen_convexity_ftc
    {F dF : RealFunRaw} {a b : Rat}
    (certificate : ConvexFTCCertificate F dF a b) :
    certificate.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      certificate.toDerivativeBoundFTC.endpointRaw := by
  exact certificate.equiv_endpoint

theorem wiedijk_item_fifteen_concavity_ftc
    {F dF : RealFunRaw} {a b : Rat}
    (certificate : ConcaveFTCCertificate F dF a b) :
    certificate.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      certificate.toDerivativeBoundFTC.endpointRaw := by
  exact certificate.equiv_endpoint

theorem wiedijk_item_fifteen_curvature_ftc
    {F dF : RealFunRaw} {a b : Rat}
    (certificate : CurvatureFTCCertificate F dF a b) :
    certificate.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      certificate.toDerivativeBoundFTC.endpointRaw := by
  exact certificate.equiv_endpoint

/-! A second public FTC foundation: a certified monotone Darboux schedule is
itself a valid raw integral, with a finite width budget for every stage. -/
theorem wiedijk_item_fifteen_monotone_darboux_integral_valid
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (schedule : Integral.MonotoneDarbouxSchedule F hregular hmonotone hinterval) :
    (Integral.monotoneDarbouxScheduleIntegralFor schedule).Valid := by
  exact Integral.monotoneDarbouxScheduleIntegralFor_valid schedule

theorem wiedijk_item_fifteen_monotone_darboux_width_budget
    {F : FunctionOnInterval} {hregular : IntervalRegularOn F}
    {hmonotone : NondecreasingOnInterval F}
    {hinterval : F.lower <= F.upper}
    (schedule : Integral.MonotoneDarbouxSchedule F hregular hmonotone hinterval)
    (n : Nat) (eps : Rat)
    (hbudget : (F.upper - F.lower) *
        (1 / ((schedule.evalPrecision n + 1 : Nat) : Rat)) <= eps) :
    ((Integral.monotoneDarbouxScheduleIntegralFor schedule).compute n).width <= eps := by
  exact Integral.monotoneDarbouxScheduleRaw_width_le_of_tolerance
    schedule n eps hbudget

theorem wiedijk_item_fifteen_effective_interval_fold_width
    (term : Nat -> QInterval) (xs : List Nat) :
    (effectiveFTCIntervalFold term xs).width =
      ratNatListSum (fun k => (term k).width) xs := by
  exact effectiveFTCIntervalFold_width term xs

theorem wiedijk_item_fifteen_square_endpoint_certificate :
    (Integral.squareEffectiveFTCData.toDerivativeBoundFTC.endpointRaw).Valid := by
  exact squareEffectiveFTC_endpointRaw_valid

theorem wiedijk_item_fifteen_cube_endpoint_certificate :
    (Integral.cubeEffectiveFTCData.toDerivativeBoundFTC.endpointRaw).Valid := by
  exact cubeEffectiveFTC_endpointRaw_valid

/-! The computable `sin²` calculus track is exposed separately from the
unfinished endpoint-value subgoal.  The function and its monotonicity are
already proved in the raw interval foundation; the final value `1/4` is only
claimed when an effective primitive certificate supplies it. -/
theorem wiedijk_item_fifteen_sin_square_function_valid
    (S : SinPiIntegral.ArctanSinPiConstruction) :
    (SinPiIntegral.sinPiSquareOnHalf S).Valid := by
  exact SinPiIntegral.sinPiSquareOnHalf_valid S

theorem wiedijk_item_fifteen_sin_square_monotone
    (S : SinPiIntegral.ArctanSinPiConstruction)
    (hsine : NondecreasingOnInterval S.onHalf) :
    NondecreasingOnInterval
      (SinPiIntegral.sinPiSquareOnHalfFunctionOnInterval S) := by
  exact SinPiIntegral.sinPiSquareOnHalf_nondecreasing_of_sine_nondecreasing
    S hsine

theorem wiedijk_item_fifteen_sin_square_effective_ftc
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (D : SinPiIntegral.SinPiSquareEffectiveFTCData S) :
    D.integralRaw.Equiv D.endpointRaw := by
  exact D.integral_equiv_endpoint

theorem wiedijk_item_fifteen_sin_square_endpoint_value_closure
    {S : SinPiIntegral.ArctanSinPiConstruction}
    (H : SinPiSquareEffectiveFTCEndpointSubgoal S) :
    H.data.integralRaw.Equiv (RealRaw.ofRat (1 / 4)) := by
  exact H.integral_value

theorem wiedijk_item_twenty_six_leibniz_series :
    Series.AlternatingRaw.leibnizAlternatingRaw.toRealRaw.Valid := by
  exact Series.AlternatingRaw.leibnizAlternatingRaw_valid

theorem wiedijk_item_twenty_six_leibniz_stage_width (n : Nat) :
    (Series.AlternatingRaw.leibnizAlternatingRaw.interval n).width =
      1 / ((4 * n + 1 : Nat) : Rat) := by
  exact Series.AlternatingRaw.leibnizAlternatingRaw_width_eq_reciprocal n

theorem wiedijk_item_twenty_six_leibniz_stage_budget
    {n : Nat} {eps : Rat} (hbudget : 1 / ((4 * n + 1 : Nat) : Rat) <= eps) :
    (Series.AlternatingRaw.leibnizAlternatingRaw.interval n).width <= eps := by
  exact Series.AlternatingRaw.leibnizAlternatingRaw_width_le_of_budget hbudget

theorem wiedijk_item_twenty_six_leibniz_precision (eps : QPos) :
    ∃ n : Nat,
      (Series.AlternatingRaw.leibnizAlternatingRaw.interval n).width <= eps.val := by
  exact Series.AlternatingRaw.leibnizAlternatingRaw_reaches_of_positive_tolerance eps

theorem wiedijk_item_thirty_five_taylor_table :
    FirstYearCalculus.PowerSeriesDerivativeEntry.hasCheckedProof
      FirstYearCalculus.PowerSeriesDerivativeEntry.exp /\
    FirstYearCalculus.PowerSeriesDerivativeEntry.hasCheckedProof
      FirstYearCalculus.PowerSeriesDerivativeEntry.sin /\
    FirstYearCalculus.PowerSeriesDerivativeEntry.hasCheckedProof
      FirstYearCalculus.PowerSeriesDerivativeEntry.negCos /\
    FirstYearCalculus.PowerSeriesDerivativeEntry.hasCheckedProof
      FirstYearCalculus.PowerSeriesDerivativeEntry.sinh /\
    FirstYearCalculus.PowerSeriesDerivativeEntry.hasCheckedProof
      FirstYearCalculus.PowerSeriesDerivativeEntry.cosh := by
  exact FirstYearCalculus.checked_power_series_table

theorem wiedijk_item_thirty_five_taylor_derivative_addition
    {F f G g : FormalPowerSeries.Coeffs}
    (hF : FormalPowerSeries.HasCoefficientShift F f)
    (hG : FormalPowerSeries.HasCoefficientShift G g) :
    FormalPowerSeries.HasCoefficientShift
      (FormalPowerSeries.add F G) (FormalPowerSeries.add f g) := by
  exact FormalPowerSeries.hasCoefficientShift_add hF hG

theorem wiedijk_item_thirty_five_taylor_derivative_rational_scaling
    (r : Rat) {F f : FormalPowerSeries.Coeffs}
    (hF : FormalPowerSeries.HasCoefficientShift F f) :
    FormalPowerSeries.HasCoefficientShift
      (FormalPowerSeries.scaleRat r F) (FormalPowerSeries.scaleRat r f) := by
  exact FormalPowerSeries.hasCoefficientShift_scaleRat r hF

def wiedijk_item_thirty_five_finite_taylor_lagrange_bridge
    (coeffs : FormalPowerSeries.Coeffs) (terms : Nat)
    (a b C : Rat) (hleft : -C <= a) (hright : b <= C)
    (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (FinitePolynomial.taylorPrefix coeffs terms) a b)
      (FunctionOnInterval.exactRat
        (FinitePolynomial.taylorPrefixShift coeffs terms) a b) := by
  exact FinitePolynomial.taylorPrefix_hasDerivativeOnInterval
    coeffs terms a b C hleft hright hC1

def wiedijk_item_thirty_five_finite_taylor_centered_bridge
    (basepoint : Rat) (coeffs : FormalPowerSeries.Coeffs)
    (terms : Nat) (a b C : Rat)
    (hleft : -C <= a - basepoint) (hright : b - basepoint <= C)
    (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (FinitePolynomial.taylorPrefixAt basepoint coeffs terms) a b)
      (FunctionOnInterval.exactRat
        (FinitePolynomial.taylorPrefixShiftAt basepoint coeffs terms) a b) := by
  exact FinitePolynomial.taylorPrefixAt_hasDerivativeOnInterval
    basepoint coeffs terms a b C hleft hright hC1

theorem wiedijk_item_thirty_five_taylor_arctan_remainder
    (x eps : Rat) (n : Nat)
    (hbudget : (x * x) ^ (n + 1) <= eps) :
    Taylor.ArctanKernel.kernelPartial x n - eps <=
        1 / (1 + x * x) /\
      1 / (1 + x * x) <=
        Taylor.ArctanKernel.kernelPartial x n + eps := by
  exact FirstYearCalculus.arctanKernel_error_box x eps n hbudget

theorem wiedijk_item_thirty_five_taylor_half_interval_precision
    {x : Rat} (hx0 : 0 <= x) (hxhalf : x <= (1 : Rat) / 2) (n : Nat) :
    1 / (1 + x * x) =
        Taylor.ArctanKernel.kernelPartial x n +
          Taylor.ArctanKernel.kernelRemainder x n /\
      qabs (Taylor.ArctanKernel.kernelRemainder x n) <=
        1 / (((n + 2 : Nat) : Rat)) := by
  exact Taylor.ArctanKernel.finite_remainder_half_interval_budget
    hx0 hxhalf n

theorem wiedijk_item_thirty_five_taylor_right_rectangle_error
    {p r : Rat}
    (hp0 : 0 <= p) (hp1 : p <= 1)
    (hpr : p <= r) (hr1 : r <= 1) (n : Nat) :
    -((n : Rat) * ((n + 1 : Nat) : Rat) * (r - p) * (r - p)) <=
        (r - p) * Taylor.ArctanKernel.kernelPartial r n -
          Taylor.ArctanKernel.kernelPartialIntegralBetween p r n /\
      (r - p) * Taylor.ArctanKernel.kernelPartial r n -
          Taylor.ArctanKernel.kernelPartialIntegralBetween p r n <=
        (n : Rat) * ((n + 1 : Nat) : Rat) * (r - p) * (r - p) := by
  exact Taylor.ArctanKernel.kernelPartial_rightRectangle_error_bound
    hp0 hp1 hpr hr1 n

theorem wiedijk_item_seventeen_de_moivre_certificate :
    RationalCircle.Trigonometry.toQComplex
        (RationalCircle.Trigonometry.pointPow
          RationalCircle.Trigonometry.deMoivreThreeFive 2) =
      QComplex.natPow
        (RationalCircle.Trigonometry.toQComplex
          RationalCircle.Trigonometry.deMoivreThreeFive) 2 := by
  exact RationalCircle.Trigonometry.deMoivreThreeFive_square_complex_bridge

/-! The finite De Moivre example is an instance of the general rational-circle
power law.  Natural powers are computed recursively and transported to
`QComplex`; no angle-valued or completed-real exponential is involved. -/
theorem wiedijk_item_seventeen_de_moivre_general
    (p : PiCirclePoint) (n : Nat) :
    RationalCircle.Trigonometry.toQComplex
        (RationalCircle.Trigonometry.pointPow p n) =
      QComplex.natPow
        (RationalCircle.Trigonometry.toQComplex p) n := by
  exact RationalCircle.Trigonometry.toQComplex_pointPow p n

theorem wiedijk_item_eight_doubling_cube_stage_twenty_four :
    (monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial).width =
      1 / 16777216 := by
  exact cubeTarget_bisection_stage24_width

theorem wiedijk_item_eight_doubling_cube_multistage_certificate :
    (cubeTarget (monotoneTargetBisectionIterate cubeTarget 2 4 cubeTargetInitial).lo <= 2 /\
      2 <= cubeTarget (monotoneTargetBisectionIterate cubeTarget 2 4 cubeTargetInitial).hi /\
      ((monotoneTargetBisectionIterate cubeTarget 2 4 cubeTargetInitial).width =
        (1 / 16 : Rat))) /\
    (cubeTarget (monotoneTargetBisectionIterate cubeTarget 2 8 cubeTargetInitial).lo <= 2 /\
      2 <= cubeTarget (monotoneTargetBisectionIterate cubeTarget 2 8 cubeTargetInitial).hi /\
      ((monotoneTargetBisectionIterate cubeTarget 2 8 cubeTargetInitial).width =
        (1 / 256 : Rat))) /\
    (cubeTarget (monotoneTargetBisectionIterate cubeTarget 2 16 cubeTargetInitial).lo <= 2 /\
      2 <= cubeTarget (monotoneTargetBisectionIterate cubeTarget 2 16 cubeTargetInitial).hi /\
      ((monotoneTargetBisectionIterate cubeTarget 2 16 cubeTargetInitial).width =
        (1 / 65536 : Rat))) /\
    (cubeTarget (monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial).lo <= 2 /\
      2 <= cubeTarget (monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial).hi /\
      ((monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial).width =
        (1 / 16777216 : Rat))) := by
  exact ⟨⟨cubeTarget_bisection_stage4_bracket.1,
      cubeTarget_bisection_stage4_bracket.2,
      cubeTarget_bisection_stage4_width⟩,
    ⟨⟨cubeTarget_bisection_stage8_bracket.1,
        cubeTarget_bisection_stage8_bracket.2,
        cubeTarget_bisection_stage8_width⟩,
      ⟨⟨cubeTarget_bisection_stage16_bracket.1,
          cubeTarget_bisection_stage16_bracket.2,
          cubeTarget_bisection_stage16_width⟩,
        ⟨cubeTarget_bisection_stage24_bracket.1,
          cubeTarget_bisection_stage24_bracket.2,
          cubeTarget_bisection_stage24_width⟩⟩⟩⟩

theorem wiedijk_item_eleven_prime_unboundedness (bound : Nat) :
    ∃ certificate : PrimeUnboundednessCertificate bound,
      bound < certificate.witness := by
  exact primeUnboundednessCertificate_exists bound

theorem wiedijk_item_ninety_eight_bertrand_finite_certificate :
    (∃ p, BasicPrime p ∧ 10 < p ∧ p < 20) /\
      (∃ p, BasicPrime p ∧ 20 < p ∧ p < 40) /\
      (∃ p, BasicPrime p ∧ 30 < p ∧ p < 60) /\
      (∃ p, BasicPrime p ∧ 40 < p ∧ p < 80) /\
      (∃ p, BasicPrime p ∧ 50 < p ∧ p < 100) := by
  exact bertrand_finite_certificate

theorem wiedijk_item_ninety_eight_prime_search_decision
    {p : Nat} (hp : 2 <= p) :
    BasicPrime p ↔ properDivisorSearch p p = none := by
  rw [basicPrime_iff_no_proper_divisor]
  exact ⟨fun h => properDivisorSearch_none_iff_no_proper.mpr h.2,
    fun h => ⟨hp, properDivisorSearch_none_iff_no_proper.mp h⟩⟩

theorem wiedijk_item_thirty_seven_cubic_witness_certificate
    (certificate : FiniteDeflationChain.CubicRootWitnessCertificate)
    (x : QComplex) :
    (IsComputableRoot certificate.coeffs
      (exactComplexCert certificate.root1)) /\
    (IsComputableRoot certificate.coeffs
      (exactComplexCert certificate.root2)) /\
    (IsComputableRoot certificate.coeffs
      (exactComplexCert certificate.root3)) /\
    CPoly.eval certificate.coeffs x =
      QComplex.mul
        (FiniteDeflationChain.rootFactorProduct
          [certificate.root1, certificate.root2, certificate.root3] x)
        (CPoly.eval
          (FiniteDeflationChain.deflatedCoeffs certificate.coeffs
            [certificate.root1, certificate.root2, certificate.root3]) x) := by
  exact certificate.computable_roots_and_factorization x

theorem wiedijk_item_thirty_seven_factorized_cubic_root_characterization
    (r s t z : QComplex) :
    CPoly.hasExactRoot (factorizedCubicPolynomial r s t) z ↔
      z = r ∨ z = s ∨ z = t := by
  exact factorizedCubicPolynomial_hasExactRoot_iff r s t z

theorem wiedijk_item_twenty_one_green_rectangle
    (left right bottom top : Rat) :
    greenRectangleBoundary left right bottom top =
      greenRectangleArea left right bottom top := by
  exact greenRectangleBoundary_eq_area left right bottom top

theorem wiedijk_item_fifty_seven_heron_squared_identity (a b c : Rat) :
    16 * ((a + b + c) / 2) * ((-a + b + c) / 2) *
        ((a - b + c) / 2) * ((a + b - c) / 2) =
      2 * (a * a) * (b * b) + 2 * (a * a) * (c * c) +
        2 * (b * b) * (c * c) - (a * a) * (a * a) -
        (b * b) * (b * b) - (c * c) * (c * c) := by
  exact RationalCircle.heron_squared_identity a b c

theorem wiedijk_item_forty_nine_cayley_hamilton_certificate :
    LinearODE.matrixAdd (LinearODE.matrixMul LinearODE.concreteCayleyMatrix
        LinearODE.concreteCayleyMatrix)
        (LinearODE.matrixAdd
          (LinearODE.matrixScale (-(LinearODE.HarmonicOscillator.twoByTwoTrace 1 2 0 3))
            LinearODE.concreteCayleyMatrix)
          (LinearODE.matrixScale (LinearODE.HarmonicOscillator.twoByTwoDeterminant 1 2 0 3)
            (LinearODE.matrixIdentity 2))) =
      LinearODE.matrixZero 2 := by
  exact LinearODE.concreteCayleyMatrix_identity_from_generic

/-! The concrete matrix above is an instance of the reusable rational
`2 x 2` Cayley--Hamilton law.  This is the project-facing theorem: its
coefficients are computed directly from the four rational entries. -/
theorem wiedijk_item_forty_nine_rational_two_by_two_cayley_hamilton
    (A : LinearODE.RatMatrix 2) :
    LinearODE.matrixAdd (LinearODE.matrixMul A A)
        (LinearODE.matrixAdd
          (LinearODE.matrixScale (-(LinearODE.HarmonicOscillator.ratMatrixTwoTrace A)) A)
          (LinearODE.matrixScale (LinearODE.HarmonicOscillator.ratMatrixTwoDeterminant A)
            (LinearODE.matrixIdentity 2))) =
      LinearODE.matrixZero 2 := by
  exact LinearODE.HarmonicOscillator.ratMatrix_twoByTwo_cayley_hamilton A

/-- The arbitrary-dimension computable boundary for Cayley--Hamilton.

The certificate carries the finite monic annihilating polynomial; the
downstream conclusion is the resulting recurrence for every matrix power.
This keeps the determinant/characteristic-polynomial construction explicit
instead of hiding classical algebra in the foundation.
-/
theorem wiedijk_item_forty_nine_arbitrary_dimension_power_recurrence
    {dimension : Nat}
    (certificate : LinearODE.FiniteCayleyHamiltonCertificate dimension)
    (steps : Nat) :
    LinearODE.matrixPow certificate.matrix
        (steps + certificate.lowerCoefficients.length) =
      LinearODE.matrixScale (-1)
        (LinearODE.matrixPolynomialSum certificate.matrix
          certificate.lowerCoefficients steps) := by
  exact certificate.power_recurrence steps

theorem wiedijk_item_fifty_five_chord_power_certificate :
    (RationalCircle.horizontalChordPowerSqrtRaw (4 / 5) 1
      (by native_decide) (by native_decide)).Equiv
      (RealRaw.ofRat (3 / 5)) := by
  exact RationalCircle.horizontalChordPowerSqrtRaw_equiv_three_fifths

theorem wiedijk_item_fifty_five_horizontal_chord_power_identity
    {r h t : Rat} (hcircle : r * r + h * h = 1) :
    (t + r) * (t - r) = t * t + h * h - 1 := by
  exact RationalCircle.horizontalChord_power_identity hcircle

theorem wiedijk_item_fifty_five_horizontal_chord_power_nonnegative
    {r t : Rat} (hr : 0 <= r) (hout : r <= t ∨ t <= -r) :
    0 <= (t + r) * (t - r) := by
  exact RationalCircle.horizontalChord_power_nonneg_of_outside hr hout

theorem wiedijk_item_forty_three_triangle_isoperimetric_bound
    {a b c : Rat}
    (h1 : 0 ≤ a + b + c) (h2 : 0 ≤ -a + b + c)
    (h3 : 0 ≤ a - b + c) (h4 : 0 ≤ a + b - c) :
    256 * RationalCircle.heronProduct a b c ≤ (a + b + c) ^ 4 := by
  exact RationalCircle.triangle_isoperimetric_heron_bound h1 h2 h3 h4

theorem wiedijk_item_forty_three_rectangle_isoperimetric
    {a b : Rat} :
    16 * rectangleArea a b ≤ rectanglePerimeter a b ^ 2 := by
  exact rectangle_isoperimetric

theorem wiedijk_item_forty_three_rectangle_isoperimetric_equality
    {a b : Rat} :
    16 * rectangleArea a b = rectanglePerimeter a b ^ 2 ↔ a = b := by
  exact rectangle_isoperimetric_eq_iff

theorem wiedijk_item_thirty_nine_pell_recurrence (stage : Nat) :
    (pellPair stage).1 * (pellPair stage).1 -
        2 * (pellPair stage).2 * (pellPair stage).2 = 1 := by
  exact pellPair_invariant stage

theorem wiedijk_item_forty_six_quartic_root_certificate :
    CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitOne /\
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitMinusOne /\
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitTwo /\
      CPoly.hasExactRoot
        (finiteQuarticQuadraticSplit quarticSplitOne quarticSplitZero
          quarticSplitMinusOne quarticSplitOne quarticSplitZero
          quarticSplitMinusFour) quarticSplitMinusTwo := by
  exact quartic_split_example_roots

theorem wiedijk_item_forty_six_factorized_quartic_root_characterization
    (r s t u z : QComplex) :
    CPoly.hasExactRoot
        (factorizedQuarticPolynomial r s t u) z ↔
      z = r ∨ z = s ∨ z = t ∨ z = u := by
  exact factorizedQuarticPolynomial_hasExactRoot_iff r s t u z

theorem wiedijk_item_twenty_three_pythagorean_triple (m n : Rat) :
    (m * m - n * n) ^ 2 + (2 * m * n) ^ 2 =
      (m * m + n * n) ^ 2 := by
  exact RationalCircle.pythagoreanTriple_identity m n

theorem wiedijk_item_forty_two_reciprocal_triangular_series :
    Series.triangularTelescopingRaw.Equiv (RealRaw.ofRat 2) := by
  exact Series.triangularTelescopingRaw_equiv_two

theorem wiedijk_item_forty_two_reciprocal_triangular_stage
    (n : Nat) :
    Series.triangularTelescopingSum n =
      2 - 2 / ((n : Rat) + 1) := by
  exact Series.triangularTelescopingSum_eq n

theorem wiedijk_item_forty_two_reciprocal_triangular_tail
    (n : Nat) :
    2 - Series.triangularTelescopingSum n =
      2 / ((n : Rat) + 1) := by
  exact Series.triangularTelescopingSum_tail_eq n

theorem wiedijk_item_thirty_four_harmonic_growth (target : Nat) :
    (target : Rat) <= FiniteHarmonic.harmonicSum (2 ^ (2 * target)) := by
  exact FiniteHarmonic.harmonicSum_two_pow_reaches target

theorem wiedijk_item_thirty_four_harmonic_stage_step (n : Nat) :
    FiniteHarmonic.harmonicSum (n + 1) =
      FiniteHarmonic.harmonicSum n + 1 / ((n + 1 : Nat) : Rat) := by
  exact FiniteHarmonic.harmonicSum_succ n

theorem wiedijk_item_thirty_four_harmonic_doubling_gain
    (n : Nat) (hn : 0 < n) :
    FiniteHarmonic.harmonicSum n + 1 / 2 <=
      FiniteHarmonic.harmonicSum (2 * n) := by
  exact FiniteHarmonic.harmonicSum_double_lower n hn

theorem wiedijk_item_thirty_four_harmonic_power_lower (k : Nat) :
    (k : Rat) / 2 <= FiniteHarmonic.harmonicSum (2 ^ k) := by
  exact FiniteHarmonic.harmonicSum_two_pow_lower k

/-! The direct computable form of harmonic divergence: a requested finite
threshold is reached by an explicit finite stage.  No infinite value is
introduced or treated as attained. -/
theorem wiedijk_item_thirty_four_harmonic_reaches_every_natural_threshold
    (target : Nat) :
    ∃ stage : Nat,
      (target : Rat) <= FiniteHarmonic.harmonicSum stage := by
  refine ⟨2 ^ (2 * target), ?_⟩
  exact FiniteHarmonic.harmonicSum_two_pow_reaches target

theorem wiedijk_item_thirty_eight_arithmetic_geometric_mean
    {a b c d : Rat}
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) (hd : 0 <= d) :
    a * b * c * d <= ((a + b + c + d) / 4) ^ 4 := by
  exact am_gm_four ha hb hc hd

theorem wiedijk_item_thirty_eight_two_variable_equality_case
    {a b : Rat} :
    a * b = ((a + b) / 2) ^ 2 ↔ a = b := by
  exact am_gm_rational_half_eq_iff

theorem wiedijk_item_sixty_five_isosceles_equal_legs (h b : Rat) :
    RationalCircle.Stage.segmentNormSq
        { x := 0, y := h } { x := b, y := 0 } =
      RationalCircle.Stage.segmentNormSq
        { x := 0, y := h } { x := -b, y := 0 } := by
  exact RationalCircle.Stage.isosceles_equal_legs h b

theorem wiedijk_item_sixty_five_isosceles_symmetry_certificate (h b : Rat) :
    RationalCircle.Stage.segmentNormSq
        { x := 0, y := h } { x := b, y := 0 } =
      RationalCircle.Stage.segmentNormSq
        { x := 0, y := h } { x := -b, y := 0 } /\
      RationalCircle.Stage.dot
        { x := 0, y := h } { x := b, y := 0 } = 0 /\
      RationalCircle.Stage.segmentNormSq
        { x := b, y := 0 } { x := -b, y := 0 } = 4 * b * b /\
      RationalCircle.Stage.segmentNormSq
        { x := 0, y := h } { x := b, y := 0 } =
          RationalCircle.Stage.segmentNormSq
            { x := 0, y := h } { x := 0, y := 0 } +
            RationalCircle.Stage.segmentNormSq
              { x := 0, y := 0 } { x := b, y := 0 } := by
  exact ⟨RationalCircle.Stage.isosceles_equal_legs h b,
    RationalCircle.Stage.isosceles_axis_orthogonal h b,
    RationalCircle.Stage.isosceles_base_normSq h b,
    RationalCircle.Stage.isosceles_axis_pythagorean h b⟩

theorem wiedijk_item_ninety_one_triangle_inequality (steps : List Rat) :
    qabs (ratListSum steps) <= ratListAbsSum steps := by
  exact RationalCircle.Stage.rationalPolyline_length_ge_straight_segment steps

theorem wiedijk_item_ninety_one_triangle_inequality_append
    (xs ys : List Rat) :
    qabs (ratListSum (xs ++ ys)) <=
      ratListAbsSum xs + ratListAbsSum ys := by
  simp only [ratListSum_append]
  calc
    qabs (ratListSum xs + ratListSum ys) <=
        qabs (ratListSum xs) + qabs (ratListSum ys) :=
      qabs_add_le (ratListSum xs) (ratListSum ys)
    _ <= ratListAbsSum xs + ratListAbsSum ys := by
      exact rat_add_le_add
        (qabs_ratListSum_le xs) (qabs_ratListSum_le ys)

theorem wiedijk_item_ninety_one_polygonal_path
    (segmentLength : PiCirclePoint -> PiCirclePoint -> Rat)
    (hzero : forall p, segmentLength p p = 0)
    (htriangle : forall p q r,
      segmentLength p r <= segmentLength p q + segmentLength q r)
    (p : PiCirclePoint) (rest : List PiCirclePoint) :
    segmentLength p
        (RationalCircle.Stage.polygonalPathEndpoint p rest) <=
      RationalCircle.Stage.polygonalPathLengthFrom segmentLength p rest := by
  exact RationalCircle.Stage.polygonalPath_length_ge_endpoint
    segmentLength hzero htriangle p rest

theorem wiedijk_item_seventy_eight_cauchy_schwarz_2d
    (a b c d : Rat) :
    (a * c + b * d) ^ 2 <=
      (a * a + b * b) * (c * c + d * d) := by
  exact cauchy_schwarz_2d a c b d

theorem wiedijk_item_seventy_eight_cauchy_schwarz_2d_equality
    (a b c d : Rat) :
    (a * b + c * d) ^ 2 =
        (a * a + c * c) * (b * b + d * d) ↔
      a * d = b * c := by
  exact cauchy_schwarz_2d_eq_iff a b c d

theorem wiedijk_item_seventy_eight_cauchy_schwarz_3d
    (a b c x y z : Rat) :
    (a * x + b * y + c * z) ^ 2 <=
      (a * a + b * b + c * c) * (x * x + y * y + z * z) := by
  exact cauchy_schwarz_3d a b c x y z

theorem wiedijk_item_seventy_eight_cauchy_schwarz_4d
    (a b c d w x y z : Rat) :
    (a * w + b * x + c * y + d * z) ^ 2 <=
      (a * a + b * b + c * c + d * d) *
        (w * w + x * x + y * y + z * z) := by
  exact cauchy_schwarz_4d a b c d w x y z

theorem wiedijk_item_seventy_eight_cauchy_schwarz_finite_lists
    {xs ys : List Rat} (hlen : xs.length = ys.length) :
    (rationalDot xs ys) ^ 2 <=
      rationalSumSquares xs * rationalSumSquares ys := by
  exact rationalDot_cauchy_schwarz_of_length_eq hlen

theorem wiedijk_item_seventy_nine_finite_intermediate_value
    (certificate : FiniteInverseSearchCertificate) :
    certificate.map certificate.output.lo ≤ certificate.target /\
      certificate.target ≤ certificate.map certificate.output.hi := by
  exact certificate.output_bracket

theorem wiedijk_item_seventy_nine_intermediate_value_midpoint_witness
    (certificate : FiniteInverseSearchCertificate) :
    certificate.map certificate.output.lo ≤ certificate.target /\
      certificate.target ≤ certificate.map certificate.output.hi /\
      certificate.output.lo ≤ certificate.output.midpoint /\
      certificate.output.midpoint ≤ certificate.output.hi := by
  exact certificate.output_midpoint_witness

theorem wiedijk_item_seventy_nine_effective_bisection
    {f : Rat -> Rat} {I : QInterval} (target : Rat)
    (hI : I.lo <= I.hi)
    (hlo : f I.lo <= target) (hhi : target <= f I.hi)
    (hwidth : I.width <= 1) (eps : QPos) :
    let J := monotoneTargetBisectionIterate f target eps.val.den I
    J.lo <= J.hi /\
      (f J.lo <= target /\ target <= f J.hi) /\
      (J.lo >= I.lo /\ J.hi <= I.hi) /\
      J.width <= eps.val := by
  exact monotoneTargetBisectionIterate_tolerance_certificate
    (f := f) (I := I) target hI hlo hhi hwidth eps

theorem wiedijk_item_seventy_nine_effective_bisection_width
    {f : Rat -> Rat} {I : QInterval} (target : Rat) (n : Nat) :
    (monotoneTargetBisectionIterate f target n I).width =
      I.width / (2 ^ n : Rat) := by
  exact monotoneTargetBisectionIterate_width target n

/-! Item 75 in its computable form: for a nonnegative-coefficient polynomial,
the secant slope is enclosed by endpoint derivative evaluations.  This is the
finite certificate that replaces the classical assertion that some attained
real point realizes the slope. -/
theorem wiedijk_item_seventy_five_effective_mean_value
    {coeffs : List Rat} {a b : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    Polynomial.finiteDerivativeEval coeffs a <=
        ExactFunction.differenceQuotient
          (fun z => Polynomial.eval coeffs z) a (b - a) /\
      ExactFunction.differenceQuotient
          (fun z => Polynomial.eval coeffs z) a (b - a) <=
        Polynomial.finiteDerivativeEval coeffs b := by
  exact Polynomial.finitePolynomial_secant_derivative_bracket
    hcoeffs ha hab hne

theorem wiedijk_item_seventy_five_local_derivative_bound_mvt
    {F dF : RealFunRaw} {a b : Rat}
    (cell : RationalSubinterval a b)
    (bound : DerivativeBoundOnSubinterval dF cell)
    (certificate : LocalFTCFromDerivativeBound F dF cell bound)
    (n : Nat) :
    (cell.scaleBound (bound.bound n)).ContainsInterval
      (endpointDifferenceInterval F cell.lower cell.upper
        (certificate.endpointPrecision n)) := by
  exact certificate.endpoint_contained n

theorem wiedijk_item_seventy_five_secant_error_bound
    {coeffs : List Rat} {a b : Rat}
    (hcoeffs : forall c, c ∈ coeffs -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0) :
    qabs (ExactFunction.differenceQuotient
      (fun z => Polynomial.eval coeffs z) a (b - a) -
        Polynomial.finiteDerivativeEval coeffs a) <=
      Polynomial.finiteDerivativeEval coeffs b -
        Polynomial.finiteDerivativeEval coeffs a := by
  exact Polynomial.finitePolynomial_secant_qabs_error_le_derivative_gap
    hcoeffs ha hab hne

theorem wiedijk_item_seventy_five_cubic_secant_enclosure
    {c₀ c₁ c₂ c₃ a b ε : Rat}
    (hcoeffs : forall c, c ∈ [c₀, c₁, c₂, c₃] -> 0 <= c)
    (ha : 0 <= a) (hab : a <= b) (hne : b - a ≠ 0)
    (hε : (2 * c₂ + 6 * c₃ * b) * (b - a) <= ε) :
    c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 <=
        ExactFunction.differenceQuotient
          (fun z => Polynomial.eval [c₀, c₁, c₂, c₃] z) a (b - a) /\
      ExactFunction.differenceQuotient
          (fun z => Polynomial.eval [c₀, c₁, c₂, c₃] z) a (b - a) <=
        c₁ + 2 * c₂ * a + 3 * c₃ * a ^ 2 + ε := by
  exact Polynomial.finiteCubic_secant_derivative_enclosure_of_budget
    hcoeffs ha hab hne hε

/-! Item 73 in its computable form: a successor inequality propagates to any
finite pair of stages.  This is the order content needed by stage algorithms;
it does not smuggle in a supremum or a completed limit. -/
theorem wiedijk_item_seventy_three_finite_monotone_sequence
    (certificate : FiniteAscendingSequenceCertificate)
    {a b : Nat} (hab : a ≤ b) :
    certificate.sequence a ≤ certificate.sequence b := by
  exact certificate.pair_le hab

theorem wiedijk_item_seventy_three_bounded_monotone_interval
    (certificate : MonotoneIntervalCertificate)
    {a b : Nat} (hab : a ≤ b) :
    certificate.loStage a ≤ certificate.loStage b /\
      certificate.loStage b ≤ certificate.hiStage b /\
      certificate.hiStage b ≤ certificate.hiStage a := by
  exact ⟨MonotoneIntervalCertificate.lower_pair_le certificate hab,
    certificate.enclosed b,
    MonotoneIntervalCertificate.upper_pair_ge certificate hab⟩

theorem wiedijk_item_seventy_three_bounded_monotone_precision
    (certificate : MonotoneIntervalCertificate) (eps : QPos) :
    ∃ N : Nat, ∀ n, N ≤ n ->
      certificate.hiStage n - certificate.loStage n <= eps.val := by
  exact certificate.width_shrinks eps

theorem wiedijk_item_seventy_three_bounded_monotone_precision_witness
    (certificate : MonotoneIntervalCertificate) (eps : QPos) :
    ∃ N : Nat, ∃ q : Rat,
      certificate.loStage N ≤ q /\
        q ≤ certificate.hiStage N /\
        certificate.hiStage N - certificate.loStage N ≤ eps.val := by
  exact certificate.precision_witness eps

/-! Item 64 in its computable form: after cancelling a common nonzero linear
factor, the quotient differs from its base value by an explicit rational
remainder.  The remainder is the finite convergence certificate; no completed
real limit is assumed. -/
theorem wiedijk_item_sixty_four_effective_lhopital
    (step numeratorConstant numeratorSlope denominatorConstant denominatorSlope : Rat)
    (hstep : step ≠ 0) (hden0 : denominatorConstant ≠ 0)
    (hden : denominatorConstant + denominatorSlope * step ≠ 0) :
    ((step * FiniteLHopitalCertificate.affineResidual
        numeratorConstant numeratorSlope step) /
        (step * FiniteLHopitalCertificate.affineResidual
          denominatorConstant denominatorSlope step)) -
      numeratorConstant / denominatorConstant =
      ((numeratorSlope * denominatorConstant - numeratorConstant * denominatorSlope) *
          step) /
        (denominatorConstant * FiniteLHopitalCertificate.affineResidual
          denominatorConstant denominatorSlope step) := by
  exact FiniteLHopitalCertificate.affine_residual_quotient_certificate
    step numeratorConstant numeratorSlope denominatorConstant denominatorSlope
    hstep hden0 hden

theorem wiedijk_item_sixty_four_lhopital_certificate_remainder
    (certificate : FiniteLHopitalCertificate.Certificate) :
    FiniteLHopitalCertificate.affineResidual
        certificate.numConst certificate.numSlope certificate.step /
        FiniteLHopitalCertificate.affineResidual
          certificate.denConst certificate.denSlope certificate.step -
      certificate.numConst / certificate.denConst =
      ((certificate.numSlope * certificate.denConst -
          certificate.numConst * certificate.denSlope) * certificate.step) /
        (certificate.denConst *
          FiniteLHopitalCertificate.affineResidual
            certificate.denConst certificate.denSlope certificate.step) := by
  exact certificate.residual_remainder_identity

theorem wiedijk_item_sixty_four_lhopital_exact_ratio
    (step numeratorConstant numeratorSlope denominatorConstant denominatorSlope : Rat)
    (hstep : step ≠ 0) (hden0 : denominatorConstant ≠ 0)
    (hden : denominatorConstant + denominatorSlope * step ≠ 0)
    (hcross : numeratorSlope * denominatorConstant -
      numeratorConstant * denominatorSlope = 0) :
    (step * FiniteLHopitalCertificate.affineResidual
        numeratorConstant numeratorSlope step) /
      (step * FiniteLHopitalCertificate.affineResidual
        denominatorConstant denominatorSlope step) =
      numeratorConstant / denominatorConstant := by
  exact FiniteLHopitalCertificate.affine_residual_quotient_eq_base_of_cross_product_eq_zero
    step numeratorConstant numeratorSlope denominatorConstant denominatorSlope
    hstep hden0 hden hcross

/-! Item 14 is already expressed at the right abstraction level in the Basel
module.  This alias records the remaining proof obligation explicitly: the
series and the geometric `pi^2 / 6` computation must overlap at every finite
stage.  The equivalence of this target with the raw-real statement is proved;
the overlap theorem itself remains an open analytic row. -/
theorem wiedijk_item_fourteen_basel_computable_target :
    Basel.eulerBasel_geometricPi ↔
      DirichletSeries.zetaTwoRaw.AllStagesOverlap
        (Basel.piSquaredOverSixRaw piCircleArea) := by
  exact Basel.eulerBasel_geometric_iff_allStagesOverlap

theorem wiedijk_item_fourteen_basel_of_stagewise_witness
    (h : forall n m : Nat, ∃ q : Rat,
      (DirichletSeries.zetaTwoRaw.compute n).lo <= q ∧
        q <= (DirichletSeries.zetaTwoRaw.compute n).hi ∧
      ((Basel.piSquaredOverSixRaw piCircleArea).compute m).lo <= q ∧
        q <= ((Basel.piSquaredOverSixRaw piCircleArea).compute m).hi) :
    Basel.eulerBasel_geometricPi := by
  exact Basel.eulerBasel_geometric_of_stagewise_witness h

theorem wiedijk_item_fourteen_basel_of_witness_certificate
    (certificate : Basel.StagewiseWitnessCertificate) :
    Basel.eulerBasel_geometricPi := by
  exact Basel.eulerBasel_geometric_of_certificate certificate

theorem wiedijk_item_fourteen_basel_finite_overlap_certificate :
    (DirichletSeries.zetaTwoInterval 200000).lo <=
        (BaselFiniteComparison.geometricPiSquaredOverSixCompute 12).hi /\
      (BaselFiniteComparison.geometricPiSquaredOverSixCompute 12).lo <=
        (DirichletSeries.zetaTwoInterval 200000).hi := by
  exact BaselFiniteComparison.zetaTwoInterval_overlaps_projectPiSquaredOverSix_200000_12

theorem wiedijk_item_fourteen_basel_high_midpoint_certificate :
    let q := BaselFiniteComparison.baselHighCommonInterval.midpoint
    (DirichletSeries.zetaTwoInterval 200000).lo <= q /\
      q <= (DirichletSeries.zetaTwoInterval 200000).hi /\
      (BaselFiniteComparison.geometricPiSquaredOverSixCompute 12).lo <= q /\
      q <= (BaselFiniteComparison.geometricPiSquaredOverSixCompute 12).hi := by
  exact BaselFiniteComparison.baselHighCommonInterval_midpoint_certificate

theorem wiedijk_item_fourteen_basel_high_common_interval_certificate :
    BaselFiniteComparison.baselHighCommonInterval.lo <=
        BaselFiniteComparison.baselHighCommonInterval.hi /\
      (DirichletSeries.zetaTwoInterval 200000).ContainsInterval
        BaselFiniteComparison.baselHighCommonInterval /\
      (BaselFiniteComparison.geometricPiSquaredOverSixCompute 12).ContainsInterval
        BaselFiniteComparison.baselHighCommonInterval := by
  exact BaselFiniteComparison.baselHighCommonInterval_certificate

theorem wiedijk_item_fourteen_basel_high_common_interval_width :
    BaselFiniteComparison.baselHighCommonInterval.width <=
        (DirichletSeries.zetaTwoInterval 200000).width /\
      BaselFiniteComparison.baselHighCommonInterval.width <=
        (BaselFiniteComparison.geometricPiSquaredOverSixCompute 12).width := by
  exact BaselFiniteComparison.baselHighCommonInterval_width_le

/-! The project-native substitute for item 14: the reciprocal-square series is
a valid raw-real algorithm and can meet every positive rational tolerance.
This is the completed computable row; the classical identification with
geometric `pi^2 / 6` remains the separate open target above. -/
theorem wiedijk_item_fourteen_effective_basel_series :
    Basel.baselSeriesRaw.Valid /\
      (forall eps : QPos, ∃ n : Nat,
        (Basel.baselSeriesRaw.compute n).width <= eps.val) := by
  exact ⟨Basel.baselSeriesRaw_valid,
    Basel.baselSeriesRaw_reaches_of_positive_tolerance⟩

/-! The series side also has an explicit all-stage tail law.  This is the
computable content available before proving that its limit equals the
geometric `pi^2 / 6` construction. -/
theorem wiedijk_item_fourteen_zeta_two_stage_tail
    {n m : Nat} (hnm : n <= m) :
    (DirichletSeries.zetaTwoInterval n).lo <=
      (DirichletSeries.zetaTwoInterval m).lo /\
      (DirichletSeries.zetaTwoInterval m).hi <=
        (DirichletSeries.zetaTwoInterval n).hi := by
  have h := DirichletSeries.zetaTwoInterval_nested n m hnm
  exact ⟨h.1, h.2.2⟩

theorem wiedijk_item_fourteen_zeta_two_width_budget
    {n : Nat} (hn : 0 < n) :
    (DirichletSeries.zetaTwoInterval n).width <= 1 / (n : Rat) := by
  exact DirichletSeries.zetaTwoInterval_width_le_one_div n hn

theorem wiedijk_item_fourteen_zeta_two_partial_tail_enclosure
    (n count : Nat) (hn : 0 < n) :
    DirichletSeries.zetaTwoPartial (n + count) <=
      (DirichletSeries.zetaTwoInterval n).hi := by
  exact DirichletSeries.zetaTwoPartial_add_finiteTail_le_interval_hi
    n count hn

/-! These are the finite tail laws behind the effective Basel evaluator.
They are the computable substitute for the analytic remainder estimate: all
quantities remain rational and every bound is valid at a named finite stage. -/
theorem wiedijk_item_fourteen_zeta_two_finite_tail_decomposition
    (n count : Nat) :
    DirichletSeries.zetaTwoPartial (n + count) =
      DirichletSeries.zetaTwoPartial n +
        DirichletSeries.zetaTwoFiniteTail n count := by
  exact DirichletSeries.zetaTwoPartial_add_finiteTail_eq n count

theorem wiedijk_item_fourteen_zeta_two_finite_tail_telescoping
    (n : Nat) (hn : 0 < n) (count : Nat) :
    DirichletSeries.zetaTwoFiniteTail n count <=
      DirichletSeries.telescopingTailBound n count := by
  exact DirichletSeries.zetaTwoFiniteTail_le_telescoping n hn count

theorem wiedijk_item_fourteen_zeta_two_nonempty_tail_strict
    (n count : Nat) (hn : 0 < n) (hcount : 0 < count) :
    DirichletSeries.zetaTwoPartial (n + count) <
      (DirichletSeries.zetaTwoInterval n).hi := by
  exact DirichletSeries.zetaTwoPartial_add_nonempty_finiteTail_lt_interval_hi
    n count hn hcount

/-! Item 76 in its finite computable form: rational samples have an exact
four-mode transform, inverse reconstruction, and Parseval energy identity.
The infinite Fourier convergence statement is intentionally not hidden inside
this certificate. -/
theorem wiedijk_item_seventy_six_finite_fourier_certificate
    (x₀ x₁ x₂ x₃ : Rat) :
    (fourPointFourierTransform x₀ x₁ x₂ x₃ 0 =
        { re := x₀ + x₁ + x₂ + x₃, im := 0 } /\
      fourPointFourierTransform x₀ x₁ x₂ x₃ 1 =
        { re := x₀ - x₂, im := x₁ - x₃ } /\
      fourPointFourierTransform x₀ x₁ x₂ x₃ 2 =
        { re := x₀ - x₁ + x₂ - x₃, im := 0 } /\
      fourPointFourierTransform x₀ x₁ x₂ x₃ 3 =
        { re := x₀ - x₂, im := x₃ - x₁ }) /\
    (let f₀ := fourPointFourierTransform x₀ x₁ x₂ x₃ 0
     let f₁ := fourPointFourierTransform x₀ x₁ x₂ x₃ 1
     let f₂ := fourPointFourierTransform x₀ x₁ x₂ x₃ 2
     let f₃ := fourPointFourierTransform x₀ x₁ x₂ x₃ 3
     f₀.re + f₁.re + f₂.re + f₃.re = 4 * x₀ /\
       f₀.re - f₂.re + f₁.im - f₃.im = 4 * x₁ /\
       f₀.re - f₁.re + f₂.re - f₃.re = 4 * x₂ /\
       f₀.re - f₂.re - f₁.im + f₃.im = 4 * x₃) /\
    QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 0) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 1) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 2) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 3) =
      4 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by
  exact ⟨fourPointFourierTransform_modes x₀ x₁ x₂ x₃,
    fourPointFourierTransform_reconstruct x₀ x₁ x₂ x₃,
    fourPointFourierTransform_parseval x₀ x₁ x₂ x₃⟩

/-! These two projections are named separately because they are the basic
finite Fourier lemmas consumed by later approximation arguments. -/
theorem wiedijk_item_seventy_six_fourier_inverse_reconstruction
    (x₀ x₁ x₂ x₃ : Rat) :
    let f₀ := fourPointFourierTransform x₀ x₁ x₂ x₃ 0
    let f₁ := fourPointFourierTransform x₀ x₁ x₂ x₃ 1
    let f₂ := fourPointFourierTransform x₀ x₁ x₂ x₃ 2
    let f₃ := fourPointFourierTransform x₀ x₁ x₂ x₃ 3
    f₀.re + f₁.re + f₂.re + f₃.re = 4 * x₀ /\
      f₀.re - f₂.re + f₁.im - f₃.im = 4 * x₁ /\
      f₀.re - f₁.re + f₂.re - f₃.re = 4 * x₂ /\
      f₀.re - f₂.re - f₁.im + f₃.im = 4 * x₃ := by
  exact fourPointFourierTransform_reconstruct x₀ x₁ x₂ x₃

theorem wiedijk_item_seventy_six_fourier_parseval
    (x₀ x₁ x₂ x₃ : Rat) :
    QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 0) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 1) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 2) +
        QComplex.normSq (fourPointFourierTransform x₀ x₁ x₂ x₃ 3) =
      4 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) := by
  exact fourPointFourierTransform_parseval x₀ x₁ x₂ x₃

theorem wiedijk_item_seventy_six_fourier_convolution
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat) :
    fourPointFourierTransform
        (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) 0 =
      QComplex.mul
        (fourPointFourierTransform x₀ x₁ x₂ x₃ 0)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ 0) /\
    fourPointFourierTransform
        (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) 1 =
      QComplex.mul
        (fourPointFourierTransform x₀ x₁ x₂ x₃ 1)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ 1) /\
    fourPointFourierTransform
        (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) 2 =
      QComplex.mul
        (fourPointFourierTransform x₀ x₁ x₂ x₃ 2)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ 2) /\
    fourPointFourierTransform
        (fourPointConvolution₀ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₁ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₂ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃)
        (fourPointConvolution₃ x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃) 3 =
      QComplex.mul
        (fourPointFourierTransform x₀ x₁ x₂ x₃ 3)
        (fourPointFourierTransform y₀ y₁ y₂ y₃ 3) := by
  exact fourPointFourierTransform_cyclic_convolution
    x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃

theorem wiedijk_item_seventy_six_fourier_mode_period_four (mode : Nat) :
    fourPointFourierSum (mode + 4) = fourPointFourierSum mode := by
  exact fourPointFourierSum_period_four mode

theorem wiedijk_item_seventy_six_fourier_mode_period_four_mul
    (mode k : Nat) :
    fourPointFourierSum (mode + 4 * k) = fourPointFourierSum mode := by
  exact fourPointFourierSum_period_four_mul mode k

theorem wiedijk_item_seventy_six_fourier_residue_orthogonality (k : Nat) :
    fourPointFourierSum (4 * k) = { re := 4, im := 0 } /\
      fourPointFourierSum (1 + 4 * k) = QComplex.zero /\
      fourPointFourierSum (2 + 4 * k) = QComplex.zero /\
      fourPointFourierSum (3 + 4 * k) = QComplex.zero := by
  exact fourPointFourierSum_four_residue k

theorem wiedijk_item_seventy_six_fourier_linear_foundation
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ r : Rat) (mode : Nat) :
    fourPointFourierTransform (x₀ + y₀) (x₁ + y₁) (x₂ + y₂) (x₃ + y₃) mode =
        QComplex.add
          (fourPointFourierTransform x₀ x₁ x₂ x₃ mode)
          (fourPointFourierTransform y₀ y₁ y₂ y₃ mode) /\
    fourPointFourierTransform (r * x₀) (r * x₁) (r * x₂) (r * x₃) mode =
        QComplex.scaleRat r
          (fourPointFourierTransform x₀ x₁ x₂ x₃ mode) /\
    fourPointFourierTransform r r r r 0 = { re := 4 * r, im := 0 } /\
    fourPointFourierTransform r r r r 1 = QComplex.zero /\
    fourPointFourierTransform r r r r 2 = QComplex.zero /\
    fourPointFourierTransform r r r r 3 = QComplex.zero := by
  exact ⟨fourPointFourierTransform_add x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ mode,
    fourPointFourierTransform_scale r x₀ x₁ x₂ x₃ mode,
    fourPointFourierTransform_constant_modes r⟩

theorem wiedijk_item_seventy_six_fourier_conjugate_symmetry
    (x₀ x₁ x₂ x₃ : Rat) :
    QComplex.conj (fourPointFourierTransform x₀ x₁ x₂ x₃ 1) =
        fourPointFourierTransform x₀ x₁ x₂ x₃ 3 /\
      QComplex.conj (fourPointFourierTransform x₀ x₁ x₂ x₃ 0) =
        fourPointFourierTransform x₀ x₁ x₂ x₃ 0 /\
      QComplex.conj (fourPointFourierTransform x₀ x₁ x₂ x₃ 2) =
        fourPointFourierTransform x₀ x₁ x₂ x₃ 2 := by
  exact fourPointFourierTransform_conjugate_symmetry x₀ x₁ x₂ x₃

theorem wiedijk_item_seventy_six_fourier_uniqueness
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : Rat)
    (h₀ : fourPointFourierTransform x₀ x₁ x₂ x₃ 0 =
      fourPointFourierTransform y₀ y₁ y₂ y₃ 0)
    (h₁ : fourPointFourierTransform x₀ x₁ x₂ x₃ 1 =
      fourPointFourierTransform y₀ y₁ y₂ y₃ 1)
    (h₂ : fourPointFourierTransform x₀ x₁ x₂ x₃ 2 =
      fourPointFourierTransform y₀ y₁ y₂ y₃ 2)
    (h₃ : fourPointFourierTransform x₀ x₁ x₂ x₃ 3 =
      fourPointFourierTransform y₀ y₁ y₂ y₃ 3) :
    x₀ = y₀ ∧ x₁ = y₁ ∧ x₂ = y₂ ∧ x₃ = y₃ := by
  exact fourPointFourierTransform_injective
    x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ h₀ h₁ h₂ h₃

theorem wiedijk_item_seventy_six_fourier_block_phase
    (root : QComplex) (mode : Nat)
    (xs ys : List QComplex) :
    finiteFourierSum root mode (xs ++ ys) =
      QComplex.add
        (finiteFourierSum root mode xs)
        (QComplex.mul
          (QComplex.natPow root (mode * xs.length))
          (finiteFourierSum root mode ys)) := by
  exact finiteFourierSum_append_phase root mode xs ys

theorem wiedijk_item_seventy_six_finite_fourier_linearity
    (root : QComplex) (mode : Nat) (r : Rat)
    (xs ys : List QComplex) :
    finiteFourierSum root mode (qcomplexListAdd xs ys) =
        QComplex.add (finiteFourierSum root mode xs)
          (finiteFourierSum root mode ys) /\
      finiteFourierSum root mode (qcomplexListScale r xs) =
        QComplex.scaleRat r (finiteFourierSum root mode xs) /\
      finiteFourierSum (QComplex.conj root) mode (qcomplexListConj xs) =
        QComplex.conj (finiteFourierSum
          root mode xs) := by
  exact ⟨finiteFourierSum_add root mode xs ys,
    finiteFourierSum_scale r root mode xs,
    (finiteFourierSum_conj root mode xs).symm⟩

theorem wiedijk_item_seventy_six_finite_fourier_cons_phase
    (root : QComplex) (mode : Nat)
    (x : QComplex) (xs : List QComplex) :
    finiteFourierSum root mode (x :: xs) =
      QComplex.add x
        (QComplex.mul
          (QComplex.natPow root mode)
          (finiteFourierSum root mode xs)) := by
  exact finiteFourierSum_cons_phase root mode x xs

theorem wiedijk_item_seventy_six_fourier_zero_mode
    (root : QComplex) (samples : List QComplex) :
    finiteFourierSum root 0 samples = qcomplexListSum samples := by
  exact finiteFourierSum_zero_mode root samples

theorem wiedijk_item_seventy_six_finite_list_mode_period_four
    (mode : Nat) (samples : List QComplex) :
    finiteFourierSum RotationSeries.imaginaryUnit (mode + 4) samples =
      finiteFourierSum RotationSeries.imaginaryUnit mode samples := by
  exact finiteFourierSum_quarterTurn_mode_period_four mode samples

theorem wiedijk_item_seventy_six_finite_list_mode_period_four_mul
    (mode k : Nat) (samples : List QComplex) :
    finiteFourierSum RotationSeries.imaginaryUnit (mode + 4 * k) samples =
      finiteFourierSum RotationSeries.imaginaryUnit mode samples := by
  exact finiteFourierSum_quarterTurn_mode_period_four_mul mode k samples

theorem wiedijk_item_seventy_six_finite_support_fourier_valid
    (root : QComplex) (mode : Nat) (samples : List QComplex) :
    (finiteSupportFourierSeries root mode samples).stabilized.Valid := by
  exact EffectiveFourierSeries.stabilized_valid
    (finiteSupportFourierSeries root mode samples)

theorem wiedijk_item_seventy_six_geometric_tail_fourier_valid
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) :
    (geometricFourierZeroModeSeries r hr0 hrhalf hr1).stabilized.Valid := by
  exact EffectiveFourierSeries.stabilized_valid
    (geometricFourierZeroModeSeries r hr0 hrhalf hr1)

theorem wiedijk_item_seventy_six_generic_fourier_tail_bridge
    (certificate : EffectiveFourierTailCertificate) :
    certificate.toSeries.stabilized.Valid := by
  exact certificate.toSeries_valid

theorem wiedijk_item_seventy_six_effective_fourier_valid
    (series : EffectiveFourierSeries) :
    series.stabilized.Valid := by
  exact series.stabilized_valid

theorem wiedijk_item_seventy_six_effective_fourier_stage_enclosure
    (series : EffectiveFourierSeries) (n : Nat) :
    (QBox.point
      (finiteFourierSum series.root series.mode (series.stage n))).NestedIn
      (series.stabilized.compute n) := by
  exact series.stage_contained n

theorem wiedijk_item_seventy_six_effective_fourier_precision
    (series : EffectiveFourierSeries) (eps : QPos) :
    ∃ N : Nat, ∀ n, N <= n ->
      (series.stabilized.compute n).width <= eps.val /\
      (series.stabilized.compute n).height <= eps.val := by
  exact (series.stabilized_valid).2.2 eps

theorem wiedijk_item_seventy_six_effective_fourier_precision_witness
    (series : EffectiveFourierSeries) (eps : QPos) :
    ∃ N : Nat, ∃ q : QComplex,
      (QBox.point q).NestedIn (series.stabilized.compute N) /\
      (series.stabilized.compute N).width <= eps.val /\
      (series.stabilized.compute N).height <= eps.val := by
  exact series.precision_witness eps

theorem wiedijk_item_seventy_six_fourier_tail_error_box
    (certificate : EffectiveFourierTailCertificate)
    (k n : Nat) (hkn : k <= n) :
    (-certificate.radius k <=
        (certificate.stage n).re - (certificate.stage k).re /\
      (certificate.stage n).re - (certificate.stage k).re <=
        certificate.radius k) /\
    (-certificate.radius k <=
        (certificate.stage n).im - (certificate.stage k).im /\
      (certificate.stage n).im - (certificate.stage k).im <=
        certificate.radius k) := by
  exact certificate.future_stage_coordinate_enclosure k n hkn

theorem wiedijk_item_seventy_six_quarter_turn_generic_tail_valid
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) :
    (quarterTurnGeometricTailCertificate r hr0 hrhalf hr1).toSeries.stabilized.Valid := by
  exact quarterTurnGeometricTailCertificate_valid r hr0 hrhalf hr1

theorem wiedijk_item_seventy_six_geometric_coefficient_stage_recurrence
    (root : QComplex) (mode : Nat) (r : Rat) (n : Nat) :
    finiteFourierSum root mode (geometricCoefficientStage r (n + 1)) =
      QComplex.add
        (finiteFourierSum root mode (geometricCoefficientStage r n))
        (QComplex.mul
          (QComplex.natPow root (mode * n))
          (QComplex.ofRat (r ^ n))) := by
  exact finiteFourierSum_geometricCoefficientStage_succ root mode r n

theorem wiedijk_item_seventy_six_quarter_turn_power_bound (n : Nat) :
    qabs ((QComplex.natPow RotationSeries.imaginaryUnit n).re) <= 1 /\
      qabs ((QComplex.natPow RotationSeries.imaginaryUnit n).im) <= 1 := by
  exact imaginaryUnit_natPow_coord_abs_le_one n

theorem wiedijk_item_seventy_six_quarter_turn_period_four (n : Nat) :
    QComplex.natPow RotationSeries.imaginaryUnit (n + 4) =
      QComplex.natPow RotationSeries.imaginaryUnit n := by
  exact imaginaryUnit_natPow_period_four n

theorem wiedijk_item_seventy_six_geometric_term_coordinate_bound
    {r : Rat} (hr0 : 0 <= r) (n : Nat) :
    qabs ((QComplex.mul (QComplex.ofRat (r ^ n))
      (QComplex.natPow RotationSeries.imaginaryUnit n)).re) <= r ^ n /\
      qabs ((QComplex.mul (QComplex.ofRat (r ^ n))
        (QComplex.natPow RotationSeries.imaginaryUnit n)).im) <= r ^ n := by
  exact quarterTurn_geometric_term_coord_abs_le hr0 n

theorem wiedijk_item_seventy_six_geometric_stage_increment_bound
    {r : Rat} (hr0 : 0 <= r) (n : Nat) :
    qabs ((quarterTurnGeometricStage r (n + 1)).re -
      (quarterTurnGeometricStage r n).re) <= r ^ n /\
    qabs ((quarterTurnGeometricStage r (n + 1)).im -
      (quarterTurnGeometricStage r n).im) <= r ^ n := by
  exact quarterTurnGeometricStage_increment_coord_abs_le hr0 n

theorem wiedijk_item_seventy_six_geometric_stage_block_tail_bound
    {r : Rat} (hr0 : 0 <= r) (n k : Nat) :
    qabs ((quarterTurnGeometricStage r (n + k)).re -
      (quarterTurnGeometricStage r n).re) <=
        r ^ n * Series.geometricSum r k /\
    qabs ((quarterTurnGeometricStage r (n + k)).im -
      (quarterTurnGeometricStage r n).im) <=
        r ^ n * Series.geometricSum r k := by
  exact quarterTurnGeometricStage_block_coord_abs_le hr0 n k

theorem wiedijk_item_seventy_six_geometric_stage_uniform_tail_bound
    {r : Rat} (hr0 : 0 <= r) (hr1 : r < 1) (n k : Nat) :
    qabs ((quarterTurnGeometricStage r (n + k)).re -
      (quarterTurnGeometricStage r n).re) <=
        r ^ n * (1 / (1 - r)) /\
    qabs ((quarterTurnGeometricStage r (n + k)).im -
      (quarterTurnGeometricStage r n).im) <=
        r ^ n * (1 / (1 - r)) := by
  exact quarterTurnGeometricStage_block_coord_abs_le_inv_one_sub hr0 hr1 n k

theorem wiedijk_item_seventy_six_quarter_turn_geometric_fourier_valid
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) :
    (quarterTurnGeometricFourierSeries r hr0 hrhalf hr1).stabilized.Valid := by
  exact EffectiveFourierSeries.stabilized_valid
    (quarterTurnGeometricFourierSeries r hr0 hrhalf hr1)

theorem wiedijk_item_seventy_six_quarter_turn_geometric_fourier_precision
    (r : Rat) (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) (eps : QPos) :
    ∃ N : Nat, ∀ n, N <= n ->
      ((quarterTurnGeometricFourierSeries r hr0 hrhalf hr1).stabilized.compute n).width
          <= eps.val /\
      ((quarterTurnGeometricFourierSeries r hr0 hrhalf hr1).stabilized.compute n).height
          <= eps.val := by
  exact (EffectiveFourierSeries.stabilized_valid
    (quarterTurnGeometricFourierSeries r hr0 hrhalf hr1)).2.2 eps

/-! Item 9 in its computable form: the circle-area interval algorithm is
valid, and agrees with the independently constructed rational rectangle
integral for the Cauchy kernel. -/
theorem wiedijk_item_nine_effective_circle_area :
    piCircleArea.Valid /\
      CauchyPi.rectangleRaw.Equiv piCircleArea := by
  exact ⟨CauchyPi.piCircleArea_valid,
    CauchyPi.rectangleRaw_equiv_piCircleArea⟩

theorem wiedijk_item_nine_circle_area_stage_ordered (n : Nat) :
    0 <= (piCircleArea.compute n).width := by
  exact (CauchyPi.piCircleArea_valid).1 n

theorem wiedijk_item_nine_circle_area_stage_nested
    {n m : Nat} (hnm : n <= m) :
    (piCircleArea.compute n).lo <= (piCircleArea.compute m).lo /\
      (piCircleArea.compute m).lo <= (piCircleArea.compute m).hi /\
      (piCircleArea.compute m).hi <= (piCircleArea.compute n).hi := by
  exact (CauchyPi.piCircleArea_valid).2.1 n m hnm

theorem wiedijk_item_nine_circle_area_precision (eps : QPos) :
    ∃ N : Nat, ∀ n, N <= n ->
      (piCircleArea.compute n).width <= eps.val := by
  exact (CauchyPi.piCircleArea_valid).2.2 eps

/-! Item 80 in its constructive finite boundary: every integer greater than one
has a terminating prime-factor certificate, and the prime membership of such a
certificate is independent of the certificate chosen. -/
theorem wiedijk_item_eighty_prime_factor_certificate {n : Nat} (hn : 1 < n) :
    Nonempty (PrimeFactorCertificate n) := by
  exact primeFactorCertificate_exists n hn

theorem wiedijk_item_eighty_prime_factor_membership_unique
    {n : Nat} (c₁ c₂ : PrimeFactorCertificate n) {p : Nat} :
    p ∈ c₁.factors ↔ p ∈ c₂.factors := by
  exact PrimeFactorCertificate.factor_mem_iff c₁ c₂

/-! Item 81 in its potential-infinity form: every finite certified list of
primes can be extended by a new prime, strictly increasing the rational
reciprocal accumulator.  This is the finite-stage content of divergence. -/
theorem wiedijk_item_eighty_one_finite_prime_reciprocal_extension
    (xs : List Nat)
    (hprime : ∀ p, p ∈ xs → BasicPrime p) :
    ∃ p, BasicPrime p ∧ p ∉ xs ∧
      primeReciprocalSum xs < primeReciprocalSum (p :: xs) := by
  exact exists_prime_reciprocal_extension xs hprime

theorem wiedijk_item_eighty_one_prime_reciprocal_extension_chain
    (xs : List Nat)
    (hprime : ∀ p, p ∈ xs → BasicPrime p) (length : Nat) :
    ∃ ys, ys.length = xs.length + length /\
      (∀ p, p ∈ ys → BasicPrime p) /\
      primeReciprocalSum xs <= primeReciprocalSum ys := by
  exact exists_prime_reciprocal_extension_chain xs hprime length

theorem wiedijk_item_eighty_one_prime_reciprocal_block_additivity
    (xs ys : List Nat) :
    primeReciprocalSum (xs ++ ys) =
      primeReciprocalSum xs + primeReciprocalSum ys := by
  exact primeReciprocalSum_append xs ys

theorem wiedijk_item_eighty_one_prime_reciprocal_exact_prefixes :
    primeReciprocalSum [2, 3, 5, 7] = 247 / 210 /\
      primeReciprocalSum [2, 3, 5, 7, 11] = 2927 / 2310 /\
      primeReciprocalSum [2, 3, 5, 7, 11, 13] = 40361 / 30030 := by
  exact ⟨primeReciprocalSum_four_primes,
    primeReciprocalSum_five_primes,
    primeReciprocalSum_six_primes⟩

theorem wiedijk_item_eighty_one_prime_reciprocal_growth_thresholds :
    (3 : Rat) / 2 <
        primeReciprocalSum
          [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] /\
      (5 : Rat) / 3 <
        primeReciprocalSum
          [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
            41, 43, 47, 53] := by
  exact ⟨primeReciprocalSum_twelve_primes_gt_three_halves,
    primeReciprocalSum_sixteen_primes_gt_five_thirds⟩

/-! Item 90 in its finite computable form: the factorial ratio used by
Stirling is enclosed by an explicit rational interval, with a certified error
bound.  The unrestricted asymptotic equivalence is intentionally not claimed
by this finite certificate. -/
theorem wiedijk_item_ninety_finite_stirling_certificate :
    qabs (finiteStirlingTenCertificate.ratioValue - 1) ≤ 1 / 100 := by
  exact finiteStirlingTenCertificate_unit_error

theorem wiedijk_item_ninety_finite_stirling_interval
    (certificate : FiniteStirlingRatioCertificate) :
    certificate.lowerBound ≤ certificate.ratioValue /\
      certificate.ratioValue ≤ certificate.upperBound := by
  exact certificate.mem_interval

theorem wiedijk_item_ninety_finite_stirling_error
    (certificate : FiniteStirlingRatioCertificate)
    (target : Rat) (hlower : target ≤ certificate.ratioValue)
    (hupper : certificate.ratioValue ≤ target + 1 / 100) :
    qabs (certificate.ratioValue - target) ≤ 1 / 100 := by
  exact certificate.abs_error_le target hlower hupper

theorem wiedijk_item_ninety_finite_stirling_error_tolerance
    (certificate : FiniteStirlingRatioCertificate)
    (target delta : Rat)
    (hlower : target ≤ certificate.ratioValue)
    (hupper : certificate.ratioValue ≤ target + delta) :
    qabs (certificate.ratioValue - target) ≤ delta := by
  exact certificate.abs_error_le_of_tolerance target delta hlower hupper

theorem wiedijk_item_ninety_finite_stirling_ratio_positive
    {n : Nat} {e root : Rat} (he : 0 < e) (hroot : 0 < root) :
    0 < finiteStirlingRatio n e root := by
  exact finiteStirlingRatio_pos he hroot

end ComputableAnalysis
