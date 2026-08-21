import ComputableAnalysis.IrrationalSqrt
import ComputableAnalysis.SqrtTwoDescent
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
import ComputableAnalysis.FiniteGeometryFormulaInterfaces
import ComputableAnalysis.FiniteCayleyHamiltonExample
import ComputableAnalysis.FiniteChordPowerExample
import ComputableAnalysis.FiniteTriangleIsoperimetricCertificate

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

theorem wiedijkScopedEntries_count : wiedijkScopedEntries.length = 52 := by
  native_decide

/-! First completed row: the benchmark statement is exposed directly through
the project's raw-real irrationality predicate, rather than Mathlib's
completed real-number predicate. -/
theorem wiedijk_item_one_sqrt_two :
    RealRaw.Irrational (sqrtRat (2 : Rat) (by native_decide)) := by
  exact sqrt_two_irrational_via_descent

theorem wiedijk_item_three_denumerability (q : Rat) :
    Exists fun n : Nat => RationalCode.decode (rationalNatCode n) = q := by
  exact rationalNatCode_decode_surjective q

theorem wiedijk_item_four_pythagorean
    (u v : PiCirclePoint) (horth : RationalCircle.Stage.dot u v = 0) :
    RationalCircle.Stage.segmentNormSq RationalCircle.Stage.origin u +
        RationalCircle.Stage.segmentNormSq RationalCircle.Stage.origin v =
      RationalCircle.Stage.segmentNormSq u v := by
  exact RationalCircle.Stage.rightTriangle_pythagorean u v horth

theorem wiedijk_item_forty_four_binomial_certificate :
    Series.binomialSum 5 2 1 6 = 243 := by
  exact binomial_stage5_two_one_value

theorem wiedijk_item_sixty_bezout (a b : Nat) :
    Exists fun x : Int =>
      Exists fun y : Int =>
        x * (a : Int) + y * (b : Int) = (Nat.gcd a b : Int) := by
  exact bezout_exists a b

theorem wiedijk_item_sixty_nine_gcd (a b : Nat) :
    euclideanGcd a b = Nat.gcd a b := by
  exact euclideanGcd_eq_gcd a b

theorem wiedijk_item_sixty_six_geometric_series
    (r : Rat) (hr : r ≠ 1) (n : Nat) :
    Series.geometricSum r n = (r ^ n - 1) / (r - 1) := by
  exact Series.geometricSum_eq r hr n

theorem wiedijk_item_sixty_eight_arithmetic_series (n : Nat) :
    Series.arithmeticSum n = (n : Rat) * ((n : Rat) - 1) / 2 := by
  exact Series.arithmeticSum_eq n

theorem wiedijk_item_seventy_seven_sum_of_squares (n : Nat) :
    Series.squareSum n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) / 6 := by
  exact Series.squareSum_eq n

/-! Item 15 is represented here by the project's effective, certificate-level
FTC portfolio.  This is deliberately a bundle of proved instances rather
than the unrestricted classical theorem for every continuous function. -/
theorem wiedijk_item_fifteen_effective_ftc : EffectiveFTCPortfolio := by
  exact effectiveFTCPortfolio

theorem wiedijk_item_twenty_six_leibniz_series :
    Series.AlternatingRaw.leibnizAlternatingRaw.toRealRaw.Valid := by
  exact Series.AlternatingRaw.leibnizAlternatingRaw_valid

theorem wiedijk_item_twenty_six_leibniz_stage_width (n : Nat) :
    (Series.AlternatingRaw.leibnizAlternatingRaw.interval n).width =
      1 / ((4 * n + 1 : Nat) : Rat) := by
  exact Series.AlternatingRaw.leibnizAlternatingRaw_width_eq_reciprocal n

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

theorem wiedijk_item_seventeen_de_moivre_certificate :
    RationalCircle.Trigonometry.toQComplex
        (RationalCircle.Trigonometry.pointPow
          RationalCircle.Trigonometry.deMoivreThreeFive 2) =
      QComplex.natPow
        (RationalCircle.Trigonometry.toQComplex
          RationalCircle.Trigonometry.deMoivreThreeFive) 2 := by
  exact RationalCircle.Trigonometry.deMoivreThreeFive_square_complex_bridge

theorem wiedijk_item_eight_doubling_cube_stage_twenty_four :
    (monotoneTargetBisectionIterate cubeTarget 2 24 cubeTargetInitial).width =
      1 / 16777216 := by
  exact cubeTarget_bisection_stage24_width

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

theorem wiedijk_item_fifty_five_chord_power_certificate :
    (RationalCircle.horizontalChordPowerSqrtRaw (4 / 5) 1
      (by native_decide) (by native_decide)).Equiv
      (RealRaw.ofRat (3 / 5)) := by
  exact RationalCircle.horizontalChordPowerSqrtRaw_equiv_three_fifths

theorem wiedijk_item_forty_three_triangle_isoperimetric_bound
    {a b c : Rat}
    (h1 : 0 ≤ a + b + c) (h2 : 0 ≤ -a + b + c)
    (h3 : 0 ≤ a - b + c) (h4 : 0 ≤ a + b - c) :
    256 * RationalCircle.heronProduct a b c ≤ (a + b + c) ^ 4 := by
  exact RationalCircle.triangle_isoperimetric_heron_bound h1 h2 h3 h4

end ComputableAnalysis
