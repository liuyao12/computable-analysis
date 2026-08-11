import ComputableAnalysis.AlgebraicNumbers

/-!
# Fundamental theorem of algebra targets

FTA sits above the algebraic-number layer.  Exact rational-complex roots and
roots of unity are supplied by `AlgebraicNumbers.lean`; this file records the
global theorem targets and small base cases.
-/

namespace ComputableAnalysis

def IsAlgebraicRoot (coeffs : CPoly.Coeffs) (z : AlgebraicComplex) : Prop :=
  IsComputableRoot coeffs z.value

/-! A finite zero-product principle for the rational coordinate model.

This is proved directly from the two rational coordinates.  It is an algebraic
fact about `QComplex`, not an appeal to an ambient completed complex field. -/
theorem QComplex.mul_eq_zero {z w : QComplex} :
    QComplex.mul z w = QComplex.zero ↔ z = QComplex.zero ∨ w = QComplex.zero := by
  constructor
  · intro h
    cases z with
    | mk zr zi =>
      cases w with
      | mk wr wi =>
        have hreal : zr * wr - zi * wi = 0 := by
          exact congrArg QComplex.re h
        have himag : zr * wi + zi * wr = 0 := by
          exact congrArg QComplex.im h
        have hsq_nonneg : ∀ x : Rat, 0 <= x * x := by
          intro x
          by_cases hx : 0 <= x
          · exact Rat.mul_nonneg hx hx
          · have hneg : 0 <= -x := by grind
            have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
            grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
        by_cases hwre : wr = 0
        · by_cases hwim : wi = 0
          · right
            subst wr
            subst wi
            rfl
          · have hzi : zi = 0 :=
              (Rat.mul_eq_zero.mp (by grind : zi * wi = 0)).resolve_right hwim
            have hzre0 : zr = 0 :=
              (Rat.mul_eq_zero.mp (by grind : zr * wi = 0)).resolve_right hwim
            left
            subst zr
            subst zi
            rfl
        · have hnorm : wr * wr + wi * wi ≠ 0 := by
            intro hnorm
            have hwi_sq : wi * wi = 0 := by
              have hwr_sq : 0 <= wr * wr := hsq_nonneg wr
              have hwi_sq' : 0 <= wi * wi := hsq_nonneg wi
              grind
            have hwr_sq : wr * wr = 0 := by grind
            have hwr0 : wr = 0 :=
              (Rat.mul_eq_zero.mp hwr_sq).resolve_right hwre
            exact hwre hwr0
          have hzre : zr * (wr * wr + wi * wi) = 0 := by
            grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
              Rat.sub_eq_add_neg]
          have hzre0 : zr = 0 :=
            (Rat.mul_eq_zero.mp hzre).resolve_right hnorm
          have hzim : zi * (wr * wr + wi * wi) = 0 := by
            grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
              Rat.sub_eq_add_neg]
          have hzim0 : zi = 0 :=
            (Rat.mul_eq_zero.mp hzim).resolve_right hnorm
          left
          subst zr
          subst zi
          rfl
  · intro h
    rcases h with hz | hw
    · rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · rw [hw]
      simp [QComplex.mul, QComplex.zero]
      grind

/-- The exact root of the monic linear polynomial `X - r`. -/
theorem monicLinear_exact_root (r : QComplex) :
    CPoly.hasExactRoot [QComplex.neg r, QComplex.one] r := by
  simp [CPoly.hasExactRoot, CPoly.eval, QComplex.add, QComplex.mul,
    QComplex.neg, QComplex.one, QComplex.zero]
  grind [Rat.sub_eq_add_neg]

theorem monicLinear_positiveDegree (r : QComplex) :
    CPoly.positiveDegree [QComplex.neg r, QComplex.one] := by
  refine Exists.intro 1 ?_
  refine Exists.intro QComplex.one ?_
  simp [QComplex.one, QComplex.zero]

/-- First constructive FTA base case: every monic linear complex polynomial
has its evident computable root. -/
theorem monicLinear_has_computable_root (r : QComplex) :
    Exists fun z : ComplexCert =>
      IsComputableRoot [QComplex.neg r, QComplex.one] z := by
  refine Exists.intro (exactComplexCert r) ?_
  exact exactRoot_is_computable (monicLinear_exact_root r)

/-- Algebraic-number version of the monic-linear base case. -/
theorem monicLinear_has_algebraic_root (r : QComplex) :
    Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot [QComplex.neg r, QComplex.one] z := by
  refine Exists.intro (AlgebraicComplex.ofQComplex r) ?_
  exact exactRoot_is_computable (monicLinear_exact_root r)

/-! An arbitrary rational-complex linear polynomial is handled whenever the
finite input supplies an inverse witness for its leading coefficient.  The
inverse is data, not an appeal to a global division operation. -/

def qcomplexLinearPolynomial (a b : QComplex) : CPoly.Coeffs :=
  [QComplex.neg b, a]

theorem qcomplexLinear_positiveDegree (a b : QComplex) (ha : a ≠ QComplex.zero) :
    CPoly.positiveDegree (qcomplexLinearPolynomial a b) := by
  refine Exists.intro 1 ?_
  refine Exists.intro a ?_
  simp [qcomplexLinearPolynomial]
  exact ha

theorem qcomplexLinear_exact_root_of_inverse
    (a b ai : QComplex) (ha : a ≠ QComplex.zero)
    (hinv : QComplex.mul a ai = QComplex.one) :
    CPoly.hasExactRoot (qcomplexLinearPolynomial a b)
      (QComplex.mul ai b) := by
  simp [CPoly.hasExactRoot, qcomplexLinearPolynomial, CPoly.eval,
    QComplex.add, QComplex.mul, QComplex.neg, QComplex.zero]
  cases a with
  | mk ar ai' =>
    cases b with
    | mk br bi =>
      cases ai with
      | mk air aii =>
        simp [QComplex.mul, QComplex.add, QComplex.neg, QComplex.one,
          QComplex.zero] at hinv ⊢
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm]

theorem qcomplexLinear_has_computable_root_of_inverse
    (a b ai : QComplex) (ha : a ≠ QComplex.zero)
    (hinv : QComplex.mul a ai = QComplex.one) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexLinearPolynomial a b) z := by
  refine ⟨exactComplexCert (QComplex.mul ai b), ?_⟩
  exact exactRoot_is_computable
    (qcomplexLinear_exact_root_of_inverse a b ai ha hinv)

theorem qcomplexLinear_has_computable_root_of_normSq
    (a b : QComplex) (hnorm : QComplex.normSq a ≠ 0) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexLinearPolynomial a b) z := by
  have ha : a ≠ QComplex.zero := by
    intro hzero
    subst a
    apply hnorm
    simp only [QComplex.normSq, QComplex.zero]
    grind
  rcases QComplex.exists_mul_inverse_of_normSq_ne_zero hnorm with ⟨ai, hinv⟩
  exact qcomplexLinear_has_computable_root_of_inverse a b ai ha hinv

theorem qcomplexLinear_has_computable_root_of_ne_zero
    (a b : QComplex) (ha : a ≠ QComplex.zero) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexLinearPolynomial a b) z := by
  apply qcomplexLinear_has_computable_root_of_normSq a b
  intro hnorm
  apply ha
  exact QComplex.normSq_eq_zero_iff.mp hnorm

def qcomplexQuadraticPolynomial (a b c : QComplex) : CPoly.Coeffs :=
  [c, b, a]

theorem qcomplexQuadratic_positiveDegree (a b c : QComplex)
    (ha : a ≠ QComplex.zero) :
    CPoly.positiveDegree (qcomplexQuadraticPolynomial a b c) := by
  refine Exists.intro 2 ?_
  refine Exists.intro a ?_
  simp [qcomplexQuadraticPolynomial]
  exact ha

theorem qcomplexQuadratic_root_of_discriminant
    (a b c d inv : QComplex)
    (hden : QComplex.mul (QComplex.scaleRat 2 a) inv = QComplex.one)
    (hdisc : QComplex.mul d d =
      QComplex.sub (QComplex.mul b b)
        (QComplex.scaleRat 4 (QComplex.mul a c))) :
    CPoly.hasExactRoot (qcomplexQuadraticPolynomial a b c)
      (QComplex.mul (QComplex.add (QComplex.neg b) d) inv) := by
  simp [CPoly.hasExactRoot, qcomplexQuadraticPolynomial, CPoly.eval,
    QComplex.add, QComplex.mul, QComplex.neg, QComplex.sub,
    QComplex.scaleRat, QComplex.one, QComplex.zero] at hden hdisc ⊢
  cases a with
  | mk ar ai =>
    cases b with
    | mk br bi =>
      cases c with
      | mk cr ci =>
        cases d with
        | mk dr di =>
          cases inv with
          | mk ir ii =>
            simp [QComplex.mul, QComplex.add, QComplex.neg, QComplex.sub,
              QComplex.scaleRat, QComplex.one, QComplex.zero] at hden hdisc ⊢
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
              Rat.mul_assoc, Rat.mul_comm]

theorem qcomplexQuadratic_has_computable_root_of_discriminant
    (a b c d inv : QComplex)
    (hden : QComplex.mul (QComplex.scaleRat 2 a) inv = QComplex.one)
    (hdisc : QComplex.mul d d =
      QComplex.sub (QComplex.mul b b)
        (QComplex.scaleRat 4 (QComplex.mul a c))) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexQuadraticPolynomial a b c) z := by
  refine ⟨exactComplexCert
    (QComplex.mul (QComplex.add (QComplex.neg b) d) inv), ?_⟩
  exact exactRoot_is_computable
    (qcomplexQuadratic_root_of_discriminant a b c d inv hden hdisc)

theorem qcomplexQuadratic_has_computable_root_of_discriminant_and_normSq
    (a b c d : QComplex) (ha : QComplex.normSq a ≠ 0)
    (hdisc : QComplex.mul d d =
      QComplex.sub (QComplex.mul b b)
        (QComplex.scaleRat 4 (QComplex.mul a c))) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexQuadraticPolynomial a b c) z := by
  have hden : QComplex.normSq (QComplex.scaleRat 2 a) ≠ 0 := by
    intro hzero
    simp [QComplex.normSq, QComplex.scaleRat] at hzero
    apply ha
    cases a with
    | mk ar ai =>
      simp [QComplex.normSq, QComplex.scaleRat] at hzero ⊢
      grind
  rcases QComplex.exists_mul_inverse_of_normSq_ne_zero hden with ⟨inv, hinv⟩
  exact qcomplexQuadratic_has_computable_root_of_discriminant
    a b c d inv hinv hdisc

theorem qcomplexQuadratic_other_root_of_discriminant
    (a b c d inv : QComplex)
    (hden : QComplex.mul (QComplex.scaleRat 2 a) inv = QComplex.one)
    (hdisc : QComplex.mul d d =
      QComplex.sub (QComplex.mul b b)
        (QComplex.scaleRat 4 (QComplex.mul a c))) :
    CPoly.hasExactRoot (qcomplexQuadraticPolynomial a b c)
      (QComplex.mul (QComplex.add (QComplex.neg b) (QComplex.neg d)) inv) := by
  apply qcomplexQuadratic_root_of_discriminant a b c (QComplex.neg d) inv hden
  cases d with
  | mk dr di =>
      simp [QComplex.mul, QComplex.neg, QComplex.sub, QComplex.add,
        QComplex.scaleRat, QComplex.one, QComplex.zero] at hdisc ⊢
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]

theorem qcomplexQuadratic_has_computable_roots_of_discriminant
    (a b c d inv : QComplex)
    (hden : QComplex.mul (QComplex.scaleRat 2 a) inv = QComplex.one)
    (hdisc : QComplex.mul d d =
      QComplex.sub (QComplex.mul b b)
        (QComplex.scaleRat 4 (QComplex.mul a c))) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexQuadraticPolynomial a b c) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexQuadraticPolynomial a b c) z) := by
  constructor
  · exact qcomplexQuadratic_has_computable_root_of_discriminant
      a b c d inv hden hdisc
  · refine ⟨exactComplexCert
      (QComplex.mul (QComplex.add (QComplex.neg b) (QComplex.neg d)) inv), ?_⟩
    exact exactRoot_is_computable
      (qcomplexQuadratic_other_root_of_discriminant a b c d inv hden hdisc)

theorem qcomplexQuadratic_has_computable_roots_of_discriminant_and_normSq
    (a b c d : QComplex) (ha : QComplex.normSq a ≠ 0)
    (hdisc : QComplex.mul d d =
      QComplex.sub (QComplex.mul b b)
        (QComplex.scaleRat 4 (QComplex.mul a c))) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexQuadraticPolynomial a b c) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (qcomplexQuadraticPolynomial a b c) z) := by
  have hden : QComplex.normSq (QComplex.scaleRat 2 a) ≠ 0 := by
    intro hzero
    simp [QComplex.normSq, QComplex.scaleRat] at hzero
    apply ha
    cases a with
    | mk ar ai =>
      simp [QComplex.normSq, QComplex.scaleRat] at hzero ⊢
      grind
  rcases QComplex.exists_mul_inverse_of_normSq_ne_zero hden with ⟨inv, hinv⟩
  exact qcomplexQuadratic_has_computable_roots_of_discriminant
    a b c d inv hinv hdisc

/-! The next finite FTA base case allows an arbitrary nonzero rational leading
coefficient.  The root is still rational, so no complex-division or isolation
algorithm is needed. -/

def rationalLinearPolynomial (a b : Rat) : CPoly.Coeffs :=
  [QComplex.ofRat b, QComplex.ofRat a]

theorem rationalLinear_positiveDegree (a b : Rat) (ha : a ≠ 0) :
    CPoly.positiveDegree (rationalLinearPolynomial a b) := by
  refine Exists.intro 1 ?_
  refine Exists.intro (QComplex.ofRat a) ?_
  simp [rationalLinearPolynomial]
  intro hzero
  have hreal := congrArg QComplex.re hzero
  simp [QComplex.ofRat, QComplex.zero] at hreal
  exact ha hreal

theorem rationalLinear_exact_root (a b : Rat) (ha : a ≠ 0) :
    CPoly.hasExactRoot (rationalLinearPolynomial a b)
      (QComplex.ofRat (-b / a)) := by
  simp [CPoly.hasExactRoot, rationalLinearPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.zero]
  rw [Rat.div_def]
  have hcancel : a * a⁻¹ = 1 := Rat.mul_inv_cancel a ha
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem rationalLinear_has_computable_root (a b : Rat) (ha : a ≠ 0) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (rationalLinearPolynomial a b) z := by
  refine Exists.intro (exactComplexCert (QComplex.ofRat (-b / a))) ?_
  exact exactRoot_is_computable (rationalLinear_exact_root a b ha)

def rationalQuadraticPolynomial (r s : Rat) : CPoly.Coeffs :=
  [QComplex.ofRat (r * s), QComplex.ofRat (-(r + s)), QComplex.one]

theorem rationalQuadratic_left_exact_root (r s : Rat) :
    CPoly.hasExactRoot (rationalQuadraticPolynomial r s)
      (QComplex.ofRat r) := by
  simp [CPoly.hasExactRoot, rationalQuadraticPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem rationalQuadratic_right_exact_root (r s : Rat) :
    CPoly.hasExactRoot (rationalQuadraticPolynomial r s)
      (QComplex.ofRat s) := by
  simp [CPoly.hasExactRoot, rationalQuadraticPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem rationalQuadratic_has_computable_roots (r s : Rat) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuadraticPolynomial r s) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuadraticPolynomial r s) z) := by
  constructor
  · exact ⟨exactComplexCert (QComplex.ofRat r),
      exactRoot_is_computable (rationalQuadratic_left_exact_root r s)⟩
  · exact ⟨exactComplexCert (QComplex.ofRat s),
      exactRoot_is_computable (rationalQuadratic_right_exact_root r s)⟩

def rationalQuadratic (a b c : Rat) : CPoly.Coeffs :=
  [QComplex.ofRat c, QComplex.ofRat b, QComplex.ofRat a]

theorem rationalQuadratic_positiveDegree (a b c : Rat) (ha : a ≠ 0) :
    CPoly.positiveDegree (rationalQuadratic a b c) := by
  refine Exists.intro 2 ?_
  refine Exists.intro (QComplex.ofRat a) ?_
  simp [rationalQuadratic]
  intro hzero
  have hreal := congrArg QComplex.re hzero
  simp [QComplex.ofRat, QComplex.zero] at hreal
  exact ha hreal

theorem rationalQuadratic_root_of_discriminant
    (a b c d : Rat) (ha : a ≠ 0)
    (hd : d ^ 2 = b ^ 2 - 4 * a * c) :
    CPoly.hasExactRoot (rationalQuadratic a b c)
      (QComplex.ofRat ((-b + d) / (2 * a))) := by
  simp [CPoly.hasExactRoot, rationalQuadratic, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.zero]
  rw [Rat.div_def]
  have hden : 2 * a ≠ 0 := by
    intro hzero
    have htwo : (2 : Rat) ≠ 0 := by native_decide
    rcases Rat.mul_eq_zero.mp hzero with htwozero | hazero
    · exact htwo htwozero
    · exact ha hazero
  have hcancel : (2 * a) * (2 * a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (2 * a) hden
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem rationalQuadratic_has_computable_root_of_discriminant
    (a b c d : Rat) (ha : a ≠ 0)
    (hd : d ^ 2 = b ^ 2 - 4 * a * c) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuadratic a b c) z := by
  refine Exists.intro
    (exactComplexCert (QComplex.ofRat ((-b + d) / (2 * a)))) ?_
  exact exactRoot_is_computable
    (rationalQuadratic_root_of_discriminant a b c d ha hd)

theorem rationalQuadratic_other_root_of_discriminant
    (a b c d : Rat) (ha : a ≠ 0)
    (hd : d ^ 2 = b ^ 2 - 4 * a * c) :
    CPoly.hasExactRoot (rationalQuadratic a b c)
      (QComplex.ofRat ((-b - d) / (2 * a))) := by
  have hdneg : (-d) ^ 2 = b ^ 2 - 4 * a * c := by
    rw [show (-d) ^ 2 = d ^ 2 by
      grind [Rat.pow_succ, Rat.mul_neg, Rat.neg_mul, Rat.neg_neg]]
    exact hd
  have hroot := rationalQuadratic_root_of_discriminant a b c (-d) ha hdneg
  simpa [Rat.sub_eq_add_neg, Rat.neg_neg] using hroot

theorem rationalQuadratic_has_computable_roots_of_discriminant
    (a b c d : Rat) (ha : a ≠ 0)
    (hd : d ^ 2 = b ^ 2 - 4 * a * c) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuadratic a b c) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuadratic a b c) z) := by
  constructor
  · refine ⟨exactComplexCert (QComplex.ofRat ((-b + d) / (2 * a))), ?_⟩
    exact exactRoot_is_computable
      (rationalQuadratic_root_of_discriminant a b c d ha hd)
  · refine ⟨exactComplexCert (QComplex.ofRat ((-b - d) / (2 * a))), ?_⟩
    exact exactRoot_is_computable
      (rationalQuadratic_other_root_of_discriminant a b c d ha hd)

theorem rationalQuadratic_has_algebraic_roots_of_discriminant
    (a b c d : Rat) (ha : a ≠ 0)
    (hd : d ^ 2 = b ^ 2 - 4 * a * c) :
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalQuadratic a b c) z) /\
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalQuadratic a b c) z) := by
  constructor
  · refine ⟨AlgebraicComplex.ofRat ((-b + d) / (2 * a)), ?_⟩
    exact exactRoot_is_computable
      (rationalQuadratic_root_of_discriminant a b c d ha hd)
  · refine ⟨AlgebraicComplex.ofRat ((-b - d) / (2 * a)), ?_⟩
    exact exactRoot_is_computable
      (rationalQuadratic_other_root_of_discriminant a b c d ha hd)

/-! A factorized quadratic over exact rational-complex coefficients gives a
generic finite root witness.  This is the first coefficient-level interface
for the factorized route: the factors, rather than a general quadratic or
quartic solver, supply the roots. -/

def factorizedQuadraticPolynomial (r s : QComplex) : CPoly.Coeffs :=
  [QComplex.mul r s, QComplex.neg (QComplex.add r s), QComplex.one]

theorem factorizedQuadratic_left_exact_root (r s : QComplex) :
    CPoly.hasExactRoot (factorizedQuadraticPolynomial r s) r := by
  simp [CPoly.hasExactRoot, factorizedQuadraticPolynomial, CPoly.eval,
    QComplex.add, QComplex.mul, QComplex.neg, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedQuadratic_right_exact_root (r s : QComplex) :
    CPoly.hasExactRoot (factorizedQuadraticPolynomial r s) s := by
  simp [CPoly.hasExactRoot, factorizedQuadraticPolynomial, CPoly.eval,
    QComplex.add, QComplex.mul, QComplex.neg, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedQuadratic_has_computable_roots (r s : QComplex) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedQuadraticPolynomial r s) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedQuadraticPolynomial r s) z) := by
  constructor
  · exact ⟨exactComplexCert r,
      exactRoot_is_computable (factorizedQuadratic_left_exact_root r s)⟩
  · exact ⟨exactComplexCert s,
      exactRoot_is_computable (factorizedQuadratic_right_exact_root r s)⟩

/-! The cubic analogue is stated over `QComplex`, rather than only over
rational real roots.  The factorization itself is the certificate: it exposes
the three supplied finite complex data and does not assert a general cubic
formula or a general fundamental theorem of algebra. -/

def factorizedCubicPolynomial (r s t : QComplex) : CPoly.Coeffs :=
  [QComplex.neg (QComplex.mul (QComplex.mul r s) t),
    QComplex.add (QComplex.add (QComplex.mul r s) (QComplex.mul r t))
      (QComplex.mul s t),
    QComplex.neg (QComplex.add (QComplex.add r s) t), QComplex.one]

theorem factorizedCubicPolynomial_eval_eq_product
    (r s t z : QComplex) :
    CPoly.eval (factorizedCubicPolynomial r s t) z =
      QComplex.mul
        (QComplex.mul (QComplex.sub z r) (QComplex.sub z s))
        (QComplex.sub z t) := by
  simp [factorizedCubicPolynomial, CPoly.eval, QComplex.add, QComplex.mul,
    QComplex.neg, QComplex.sub, QComplex.one, QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem factorizedCubicPolynomial_eval_eq_zero_iff
    (r s t z : QComplex) :
    CPoly.eval (factorizedCubicPolynomial r s t) z = QComplex.zero ↔
      z = r ∨ z = s ∨ z = t := by
  have hsub : ∀ u v : QComplex,
      QComplex.sub u v = QComplex.zero ↔ u = v := by
    intro u v
    cases u
    cases v
    simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
    grind [Rat.sub_eq_add_neg]
  rw [factorizedCubicPolynomial_eval_eq_product]
  constructor
  · intro h
    rcases QComplex.mul_eq_zero.mp h with hleft | hright
    · rcases QComplex.mul_eq_zero.mp hleft with hrs | hst
      · exact Or.inl (hsub z r |>.mp hrs)
      · exact Or.inr (Or.inl (hsub z s |>.mp hst))
    · exact Or.inr (Or.inr (hsub z t |>.mp hright))
  · intro h
    rcases h with h | h | h
    · have hz : QComplex.sub z r = QComplex.zero := (hsub z r).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z s = QComplex.zero := (hsub z s).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z t = QComplex.zero := (hsub z t).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind

theorem factorizedCubicPolynomial_hasExactRoot_iff
    (r s t z : QComplex) :
    CPoly.hasExactRoot (factorizedCubicPolynomial r s t) z ↔
      z = r ∨ z = s ∨ z = t := by
  change CPoly.eval (factorizedCubicPolynomial r s t) z = QComplex.zero ↔ _
  exact factorizedCubicPolynomial_eval_eq_zero_iff r s t z

theorem factorizedCubic_left_exact_root (r s t : QComplex) :
    CPoly.hasExactRoot (factorizedCubicPolynomial r s t) r := by
  change CPoly.eval (factorizedCubicPolynomial r s t) r = QComplex.zero
  rw [factorizedCubicPolynomial_eval_eq_product]
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero, QComplex.mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedCubic_middle_exact_root (r s t : QComplex) :
    CPoly.hasExactRoot (factorizedCubicPolynomial r s t) s := by
  change CPoly.eval (factorizedCubicPolynomial r s t) s = QComplex.zero
  rw [factorizedCubicPolynomial_eval_eq_product]
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero, QComplex.mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedCubic_right_exact_root (r s t : QComplex) :
    CPoly.hasExactRoot (factorizedCubicPolynomial r s t) t := by
  change CPoly.eval (factorizedCubicPolynomial r s t) t = QComplex.zero
  rw [factorizedCubicPolynomial_eval_eq_product]
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero, QComplex.mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedCubic_has_computable_roots (r s t : QComplex) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedCubicPolynomial r s t) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedCubicPolynomial r s t) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedCubicPolynomial r s t) z) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨exactComplexCert r,
      exactRoot_is_computable (factorizedCubic_left_exact_root r s t)⟩
  · exact ⟨exactComplexCert s,
      exactRoot_is_computable (factorizedCubic_middle_exact_root r s t)⟩
  · exact ⟨exactComplexCert t,
      exactRoot_is_computable (factorizedCubic_right_exact_root r s t)⟩

/-! The quartic analogue keeps the same finite certificate boundary: four
supplied rational-complex factors expose four exact roots.  This is a
factorization characterization, not a general quartic formula or an
arbitrary-degree FTA theorem. -/

def factorizedQuarticPolynomial (r s t u : QComplex) : CPoly.Coeffs :=
  [QComplex.mul (QComplex.mul (QComplex.mul r s) t) u,
    QComplex.neg
      (QComplex.add
        (QComplex.add (QComplex.mul (QComplex.mul r s) t)
          (QComplex.mul (QComplex.mul r s) u))
        (QComplex.add (QComplex.mul (QComplex.mul r t) u)
          (QComplex.mul (QComplex.mul s t) u))),
    QComplex.add
      (QComplex.add
        (QComplex.add (QComplex.mul r s) (QComplex.mul r t))
        (QComplex.mul r u))
      (QComplex.add
        (QComplex.add (QComplex.mul s t) (QComplex.mul s u))
        (QComplex.mul t u)),
    QComplex.neg
      (QComplex.add (QComplex.add r s) (QComplex.add t u)), QComplex.one]

theorem factorizedQuarticPolynomial_eval_eq_product
    (r s t u z : QComplex) :
    CPoly.eval (factorizedQuarticPolynomial r s t u) z =
      QComplex.mul
        (QComplex.mul
          (QComplex.mul (QComplex.sub z r) (QComplex.sub z s))
          (QComplex.sub z t))
        (QComplex.sub z u) := by
  simp [factorizedQuarticPolynomial, CPoly.eval, QComplex.add, QComplex.mul,
    QComplex.neg, QComplex.sub, QComplex.one, QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem factorizedQuarticPolynomial_eval_eq_zero_iff
    (r s t u z : QComplex) :
    CPoly.eval (factorizedQuarticPolynomial r s t u) z = QComplex.zero ↔
      z = r ∨ z = s ∨ z = t ∨ z = u := by
  have hsub : ∀ x y : QComplex,
      QComplex.sub x y = QComplex.zero ↔ x = y := by
    intro x y
    cases x
    cases y
    simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
    grind [Rat.sub_eq_add_neg]
  rw [factorizedQuarticPolynomial_eval_eq_product]
  constructor
  · intro h
    rcases QComplex.mul_eq_zero.mp h with hleft | hright
    · rcases QComplex.mul_eq_zero.mp hleft with hleft | hthird
      · rcases QComplex.mul_eq_zero.mp hleft with hfirst | hsecond
        · exact Or.inl (hsub z r |>.mp hfirst)
        · exact Or.inr (Or.inl (hsub z s |>.mp hsecond))
      · exact Or.inr (Or.inr (Or.inl (hsub z t |>.mp hthird)))
    · exact Or.inr (Or.inr (Or.inr (hsub z u |>.mp hright)))
  · intro h
    rcases h with h | h | h | h
    · have hz : QComplex.sub z r = QComplex.zero := (hsub z r).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z s = QComplex.zero := (hsub z s).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z t = QComplex.zero := (hsub z t).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z u = QComplex.zero := (hsub z u).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind

theorem factorizedQuarticPolynomial_hasExactRoot_iff
    (r s t u z : QComplex) :
    CPoly.hasExactRoot (factorizedQuarticPolynomial r s t u) z ↔
      z = r ∨ z = s ∨ z = t ∨ z = u := by
  change CPoly.eval (factorizedQuarticPolynomial r s t u) z = QComplex.zero ↔ _
  exact factorizedQuarticPolynomial_eval_eq_zero_iff r s t u z

theorem factorizedQuartic_left_exact_root (r s t u : QComplex) :
    CPoly.hasExactRoot (factorizedQuarticPolynomial r s t u) r := by
  change CPoly.eval (factorizedQuarticPolynomial r s t u) r = QComplex.zero
  rw [factorizedQuarticPolynomial_eval_eq_product]
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero, QComplex.mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedQuartic_second_exact_root (r s t u : QComplex) :
    CPoly.hasExactRoot (factorizedQuarticPolynomial r s t u) s := by
  change CPoly.eval (factorizedQuarticPolynomial r s t u) s = QComplex.zero
  rw [factorizedQuarticPolynomial_eval_eq_product]
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero, QComplex.mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedQuartic_third_exact_root (r s t u : QComplex) :
    CPoly.hasExactRoot (factorizedQuarticPolynomial r s t u) t := by
  change CPoly.eval (factorizedQuarticPolynomial r s t u) t = QComplex.zero
  rw [factorizedQuarticPolynomial_eval_eq_product]
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero, QComplex.mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedQuartic_right_exact_root (r s t u : QComplex) :
    CPoly.hasExactRoot (factorizedQuarticPolynomial r s t u) u := by
  change CPoly.eval (factorizedQuarticPolynomial r s t u) u = QComplex.zero
  rw [factorizedQuarticPolynomial_eval_eq_product]
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero, QComplex.mul]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem factorizedQuartic_has_computable_roots (r s t u : QComplex) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedQuarticPolynomial r s t u) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedQuarticPolynomial r s t u) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedQuarticPolynomial r s t u) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedQuarticPolynomial r s t u) z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨exactComplexCert r,
      exactRoot_is_computable (factorizedQuartic_left_exact_root r s t u)⟩
  · exact ⟨exactComplexCert s,
      exactRoot_is_computable (factorizedQuartic_second_exact_root r s t u)⟩
  · exact ⟨exactComplexCert t,
      exactRoot_is_computable (factorizedQuartic_third_exact_root r s t u)⟩
  · exact ⟨exactComplexCert u,
      exactRoot_is_computable (factorizedQuartic_right_exact_root r s t u)⟩

/-! A factorized rational cubic gives the next finite constructive FTA base
case.  Its three roots are explicit, so no general cubic formula is needed. -/

def rationalCubicPolynomial (r s t : Rat) : CPoly.Coeffs :=
  [QComplex.ofRat (-(r * s * t)),
    QComplex.ofRat (r * s + r * t + s * t),
    QComplex.ofRat (-(r + s + t)), QComplex.one]

theorem rationalCubic_positiveDegree (r s t : Rat) :
    CPoly.positiveDegree (rationalCubicPolynomial r s t) := by
  refine Exists.intro 3 ?_
  refine Exists.intro QComplex.one ?_
  simp [rationalCubicPolynomial, QComplex.one, QComplex.zero]

theorem rationalCubic_left_exact_root (r s t : Rat) :
    CPoly.hasExactRoot (rationalCubicPolynomial r s t)
      (QComplex.ofRat r) := by
  simp [CPoly.hasExactRoot, rationalCubicPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem rationalCubic_middle_exact_root (r s t : Rat) :
    CPoly.hasExactRoot (rationalCubicPolynomial r s t)
      (QComplex.ofRat s) := by
  simp [CPoly.hasExactRoot, rationalCubicPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem rationalCubic_right_exact_root (r s t : Rat) :
    CPoly.hasExactRoot (rationalCubicPolynomial r s t)
      (QComplex.ofRat t) := by
  simp [CPoly.hasExactRoot, rationalCubicPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem rationalCubic_has_computable_roots (r s t : Rat) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalCubicPolynomial r s t) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalCubicPolynomial r s t) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalCubicPolynomial r s t) z) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨exactComplexCert (QComplex.ofRat r),
      exactRoot_is_computable (rationalCubic_left_exact_root r s t)⟩
  · exact ⟨exactComplexCert (QComplex.ofRat s),
      exactRoot_is_computable (rationalCubic_middle_exact_root r s t)⟩
  · exact ⟨exactComplexCert (QComplex.ofRat t),
      exactRoot_is_computable (rationalCubic_right_exact_root r s t)⟩

theorem rationalCubic_has_algebraic_roots (r s t : Rat) :
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalCubicPolynomial r s t) z) /\
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalCubicPolynomial r s t) z) /\
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalCubicPolynomial r s t) z) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨AlgebraicComplex.ofRat r,
      exactRoot_is_computable (rationalCubic_left_exact_root r s t)⟩
  · exact ⟨AlgebraicComplex.ofRat s,
      exactRoot_is_computable (rationalCubic_middle_exact_root r s t)⟩
  · exact ⟨AlgebraicComplex.ofRat t,
      exactRoot_is_computable (rationalCubic_right_exact_root r s t)⟩

/-! The same factorized construction supplies a finite quartic worked core. -/

def rationalQuarticPolynomial (r s t u : Rat) : CPoly.Coeffs :=
  [QComplex.ofRat (r * s * t * u),
    QComplex.ofRat (-(r * s * t + r * s * u + r * t * u + s * t * u)),
    QComplex.ofRat (r * s + r * t + r * u + s * t + s * u + t * u),
    QComplex.ofRat (-(r + s + t + u)), QComplex.one]

theorem rationalQuartic_positiveDegree (r s t u : Rat) :
    CPoly.positiveDegree (rationalQuarticPolynomial r s t u) := by
  refine Exists.intro 4 ?_
  refine Exists.intro QComplex.one ?_
  simp [rationalQuarticPolynomial, QComplex.one, QComplex.zero]

theorem rationalQuartic_left_exact_root (r s t u : Rat) :
    CPoly.hasExactRoot (rationalQuarticPolynomial r s t u)
      (QComplex.ofRat r) := by
  simp [CPoly.hasExactRoot, rationalQuarticPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem rationalQuartic_second_exact_root (r s t u : Rat) :
    CPoly.hasExactRoot (rationalQuarticPolynomial r s t u)
      (QComplex.ofRat s) := by
  simp [CPoly.hasExactRoot, rationalQuarticPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem rationalQuartic_third_exact_root (r s t u : Rat) :
    CPoly.hasExactRoot (rationalQuarticPolynomial r s t u)
      (QComplex.ofRat t) := by
  simp [CPoly.hasExactRoot, rationalQuarticPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem rationalQuartic_right_exact_root (r s t u : Rat) :
    CPoly.hasExactRoot (rationalQuarticPolynomial r s t u)
      (QComplex.ofRat u) := by
  simp [CPoly.hasExactRoot, rationalQuarticPolynomial, CPoly.eval,
    QComplex.ofRat, QComplex.add, QComplex.mul, QComplex.one,
    QComplex.zero]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.pow_succ]

theorem rationalQuartic_has_computable_roots (r s t u : Rat) :
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuarticPolynomial r s t u) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuarticPolynomial r s t u) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuarticPolynomial r s t u) z) /\
    (Exists fun z : ComplexCert =>
      IsComputableRoot (rationalQuarticPolynomial r s t u) z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨exactComplexCert (QComplex.ofRat r),
      exactRoot_is_computable (rationalQuartic_left_exact_root r s t u)⟩
  · exact ⟨exactComplexCert (QComplex.ofRat s),
      exactRoot_is_computable (rationalQuartic_second_exact_root r s t u)⟩
  · exact ⟨exactComplexCert (QComplex.ofRat t),
      exactRoot_is_computable (rationalQuartic_third_exact_root r s t u)⟩
  · exact ⟨exactComplexCert (QComplex.ofRat u),
      exactRoot_is_computable (rationalQuartic_right_exact_root r s t u)⟩

theorem rationalQuartic_has_algebraic_roots (r s t u : Rat) :
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalQuarticPolynomial r s t u) z) /\
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalQuarticPolynomial r s t u) z) /\
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalQuarticPolynomial r s t u) z) /\
    (Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (rationalQuarticPolynomial r s t u) z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨AlgebraicComplex.ofRat r,
      exactRoot_is_computable (rationalQuartic_left_exact_root r s t u)⟩
  · exact ⟨AlgebraicComplex.ofRat s,
      exactRoot_is_computable (rationalQuartic_second_exact_root r s t u)⟩
  · exact ⟨AlgebraicComplex.ofRat t,
      exactRoot_is_computable (rationalQuartic_third_exact_root r s t u)⟩
  · exact ⟨AlgebraicComplex.ofRat u,
      exactRoot_is_computable (rationalQuartic_right_exact_root r s t u)⟩

/-! A generic finite factorized polynomial over `QComplex`.

The coefficient list is stored in constant-first order, as in `CPoly.eval`.
`factorizedPolynomial` is built by finite recursion from the supplied roots:
each step multiplies the current coefficient list by the linear factor
`X - r`.  Thus this is a finite factorization certificate, not an arbitrary
polynomial solver or an appeal to the Fundamental Theorem of Algebra. -/

def cpolyAdd : CPoly.Coeffs -> CPoly.Coeffs -> CPoly.Coeffs
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => QComplex.add x y :: cpolyAdd xs ys

def cpolyScale (c : QComplex) (p : CPoly.Coeffs) : CPoly.Coeffs :=
  p.map (fun a => QComplex.mul c a)

def cpolyShift (p : CPoly.Coeffs) : CPoly.Coeffs :=
  QComplex.zero :: p

def cpolyLinearMultiply (r : QComplex) (p : CPoly.Coeffs) : CPoly.Coeffs :=
  cpolyAdd (cpolyScale (QComplex.neg r) p) (cpolyShift p)

def factorizedPolynomial : List QComplex -> CPoly.Coeffs
  | [] => [QComplex.one]
  | r :: rs => cpolyLinearMultiply r (factorizedPolynomial rs)

theorem CPoly.eval_cons (c : QComplex) (p : CPoly.Coeffs) (z : QComplex) :
    CPoly.eval (c :: p) z =
      QComplex.add c (QComplex.mul z (CPoly.eval p z)) := rfl

theorem CPoly.eval_cpolyAdd (p q : CPoly.Coeffs) (z : QComplex) :
    CPoly.eval (cpolyAdd p q) z =
      QComplex.add (CPoly.eval p z) (CPoly.eval q z) := by
  induction p generalizing q with
  | nil =>
      change CPoly.eval q z = QComplex.add (CPoly.eval [] z) (CPoly.eval q z)
      simp only [CPoly.eval, List.foldr]
      cases h : List.foldr (fun c acc =>
        QComplex.add c (QComplex.mul z acc)) QComplex.zero q
      simp [QComplex.add, QComplex.zero]
      grind
  | cons x xs ih =>
      cases q with
      | nil =>
          change CPoly.eval (x :: xs) z =
            QComplex.add (CPoly.eval (x :: xs) z) (CPoly.eval [] z)
          rw [CPoly.eval_cons]
          simp only [CPoly.eval, List.foldr]
          cases h : List.foldr (fun c acc =>
            QComplex.add c (QComplex.mul z acc)) QComplex.zero xs
          simp [QComplex.add, QComplex.zero]
          grind
      | cons y ys =>
          change CPoly.eval (QComplex.add x y :: cpolyAdd xs ys) z = _
          rw [CPoly.eval_cons, CPoly.eval_cons, CPoly.eval_cons]
          rw [ih ys]
          simp [QComplex.add, QComplex.mul]
          grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
            Rat.mul_add, Rat.add_mul]

theorem CPoly.eval_cpolyScale (c : QComplex) (p : CPoly.Coeffs) (z : QComplex) :
    CPoly.eval (cpolyScale c p) z =
      QComplex.mul c (CPoly.eval p z) := by
  induction p with
  | nil =>
      simp [cpolyScale, CPoly.eval, QComplex.zero, QComplex.mul]
      grind
  | cons x xs ih =>
      change CPoly.eval (QComplex.mul c x :: cpolyScale c xs) z = _
      rw [CPoly.eval_cons, CPoly.eval_cons]
      rw [ih]
      simp [QComplex.add, QComplex.mul]
      grind [Rat.add_mul, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

theorem CPoly.eval_cpolyShift (p : CPoly.Coeffs) (z : QComplex) :
    CPoly.eval (cpolyShift p) z = QComplex.mul z (CPoly.eval p z) := by
  rw [show cpolyShift p = QComplex.zero :: p by rfl, CPoly.eval_cons]
  cases h : CPoly.eval p z
  simp [QComplex.zero, QComplex.add, QComplex.mul]
  grind

theorem CPoly.eval_cpolyLinearMultiply (r : QComplex) (p : CPoly.Coeffs)
    (z : QComplex) :
    CPoly.eval (cpolyLinearMultiply r p) z =
      QComplex.mul (QComplex.sub z r) (CPoly.eval p z) := by
  rw [cpolyLinearMultiply, CPoly.eval_cpolyAdd,
    CPoly.eval_cpolyScale, CPoly.eval_cpolyShift]
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.mul]
  grind [Rat.add_mul, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm,
    Rat.neg_mul, Rat.mul_neg]

theorem factorizedPolynomial_eval_eq_product
    (roots : List QComplex) (z : QComplex) :
    CPoly.eval (factorizedPolynomial roots) z =
      roots.foldr (fun r acc =>
        QComplex.mul (QComplex.sub z r) acc) QComplex.one := by
  induction roots with
  | nil =>
      rw [show factorizedPolynomial [] = [QComplex.one] by rfl,
        CPoly.eval_cons]
      cases z
      simp [CPoly.eval, QComplex.one, QComplex.zero, QComplex.add,
        QComplex.mul]
      grind
  | cons r rs ih =>
      simp only [factorizedPolynomial]
      rw [CPoly.eval_cpolyLinearMultiply, ih]
      rfl

/-! A finite zero-product principle for the rational coordinate model.

This is proved directly from the two rational coordinates.  It is an algebraic
fact about `QComplex`, not an appeal to an ambient completed complex field. -/
theorem QComplex.mul_eq_zero_late {z w : QComplex} :
    QComplex.mul z w = QComplex.zero ↔ z = QComplex.zero ∨ w = QComplex.zero := by
  constructor
  · intro h
    cases z with
    | mk zr zi =>
      cases w with
      | mk wr wi =>
        have hreal : zr * wr - zi * wi = 0 := by
          exact congrArg QComplex.re h
        have himag : zr * wi + zi * wr = 0 := by
          exact congrArg QComplex.im h
        have hsq_nonneg : ∀ x : Rat, 0 <= x * x := by
          intro x
          by_cases hx : 0 <= x
          · exact Rat.mul_nonneg hx hx
          · have hneg : 0 <= -x := by grind
            have hsq : 0 <= (-x) * (-x) := Rat.mul_nonneg hneg hneg
            grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
        by_cases hwre : wr = 0
        · by_cases hwim : wi = 0
          · right
            subst wr
            subst wi
            rfl
          · have hzi : zi = 0 :=
              (Rat.mul_eq_zero.mp (by grind : zi * wi = 0)).resolve_right hwim
            have hzre0 : zr = 0 :=
              (Rat.mul_eq_zero.mp (by grind : zr * wi = 0)).resolve_right hwim
            left
            subst zr
            subst zi
            rfl
        · have hnorm : wr * wr + wi * wi ≠ 0 := by
            intro hnorm
            have hwi_sq : wi * wi = 0 := by
              have hwr_sq : 0 <= wr * wr := hsq_nonneg wr
              have hwi_sq' : 0 <= wi * wi := hsq_nonneg wi
              grind
            have hwr_sq : wr * wr = 0 := by grind
            have hwr0 : wr = 0 :=
              (Rat.mul_eq_zero.mp hwr_sq).resolve_right hwre
            exact hwre hwr0
          have hzre : zr * (wr * wr + wi * wi) = 0 := by
            grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
              Rat.sub_eq_add_neg]
          have hzre0 : zr = 0 :=
            (Rat.mul_eq_zero.mp hzre).resolve_right hnorm
          have hzim : zi * (wr * wr + wi * wi) = 0 := by
            grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
              Rat.sub_eq_add_neg]
          have hzim0 : zi = 0 :=
            (Rat.mul_eq_zero.mp hzim).resolve_right hnorm
          left
          subst zr
          subst zi
          rfl
  · intro h
    rcases h with hz | hw
    · rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · rw [hw]
      simp [QComplex.mul, QComplex.zero]
      grind

theorem factorizedPolynomial_eval_eq_zero_iff_mem
    {roots : List QComplex} {z : QComplex} :
    CPoly.eval (factorizedPolynomial roots) z = QComplex.zero ↔ z ∈ roots := by
  rw [factorizedPolynomial_eval_eq_product]
  induction roots with
  | nil =>
      simp [QComplex.one, QComplex.zero]
  | cons r roots ih =>
      simp only [List.foldr]
      rw [QComplex.mul_eq_zero, ih]
      have hsub : QComplex.sub z r = QComplex.zero ↔ z = r := by
        cases z
        cases r
        simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
        grind [Rat.sub_eq_add_neg]
      rw [hsub]
      simp only [List.mem_cons]

theorem factorizedPolynomial_hasExactRoot_iff_mem
    {roots : List QComplex} {z : QComplex} :
    CPoly.hasExactRoot (factorizedPolynomial roots) z ↔ z ∈ roots := by
  change CPoly.eval (factorizedPolynomial roots) z = QComplex.zero ↔ z ∈ roots
  exact factorizedPolynomial_eval_eq_zero_iff_mem

theorem factorizedQuadraticPolynomial_hasExactRoot_iff
    (r s z : QComplex) :
    CPoly.hasExactRoot (factorizedQuadraticPolynomial r s) z ↔
      z = r ∨ z = s := by
  have hpoly : factorizedQuadraticPolynomial r s =
      factorizedPolynomial [r, s] := by
    simp [factorizedQuadraticPolynomial, factorizedPolynomial,
      cpolyLinearMultiply, cpolyScale, cpolyShift, cpolyAdd,
      QComplex.add, QComplex.mul, QComplex.neg, QComplex.one,
      QComplex.zero]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  change CPoly.eval (factorizedQuadraticPolynomial r s) z =
    QComplex.zero ↔ _
  rw [hpoly]
  simpa using (factorizedPolynomial_eval_eq_zero_iff_mem
    (roots := [r, s]) (z := z))

theorem factorizedPolynomial_exact_root_of_mem
    {roots : List QComplex} {r : QComplex} (hr : r ∈ roots) :
    CPoly.hasExactRoot (factorizedPolynomial roots) r := by
  change CPoly.eval (factorizedPolynomial roots) r = QComplex.zero
  rw [factorizedPolynomial_eval_eq_product]
  induction roots with
  | nil => cases hr
  | cons a roots ih =>
      simp only [List.mem_cons] at hr
      simp only [List.foldr]
      rcases hr with rfl | hr
      · cases r with
        | mk re im =>
            have hsub : QComplex.sub { re := re, im := im }
                { re := re, im := im } = QComplex.zero := by
              simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
              grind [Rat.sub_eq_add_neg]
            rw [hsub]
            cases h : List.foldr (fun r acc =>
              QComplex.mul (QComplex.sub { re := re, im := im } r) acc)
              QComplex.one roots
            simp [QComplex.mul, QComplex.zero]
            grind
      · rw [ih hr]
        simp [QComplex.mul, QComplex.zero]
        grind

theorem factorizedPolynomial_computable_root_of_mem
    {roots : List QComplex} {r : QComplex} (hr : r ∈ roots) :
    IsComputableRoot (factorizedPolynomial roots) (exactComplexCert r) := by
  exact exactRoot_is_computable (factorizedPolynomial_exact_root_of_mem hr)

/-- Every supplied factor is returned as a computable root, packaged as a
finite list-level certificate. -/
theorem factorizedPolynomial_all_computable_roots
    (roots : List QComplex) :
    ∀ r, r ∈ roots ->
      IsComputableRoot (factorizedPolynomial roots) (exactComplexCert r) := by
  intro r hr
  exact factorizedPolynomial_computable_root_of_mem hr

theorem factorizedPolynomial_has_algebraic_root_of_nonempty
    {roots : List QComplex} (hroots : roots ≠ []) :
    Exists fun z : AlgebraicComplex =>
      IsAlgebraicRoot (factorizedPolynomial roots) z := by
  cases roots with
  | nil => exact False.elim (hroots rfl)
  | cons r rs =>
      refine ⟨AlgebraicComplex.ofQComplex r, ?_⟩
      exact exactRoot_is_computable
        (factorizedPolynomial_exact_root_of_mem (by simp))

theorem factorizedPolynomial_has_computable_root_of_nonempty
    {roots : List QComplex} (hroots : roots ≠ []) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedPolynomial roots) z := by
  cases roots with
  | nil => exact False.elim (hroots rfl)
  | cons r rs =>
      refine ⟨exactComplexCert r, ?_⟩
      exact factorizedPolynomial_computable_root_of_mem (by simp)

theorem factorizedPolynomial_algebraic_root_of_mem
    {roots : List QComplex} {r : QComplex} (hr : r ∈ roots) :
    IsAlgebraicRoot (factorizedPolynomial roots)
      (AlgebraicComplex.ofQComplex r) := by
  exact exactRoot_is_computable (factorizedPolynomial_exact_root_of_mem hr)

/-! An executable finite search over supplied candidate roots.

`exactRootSearch` is deliberately coefficient-generic: it scans a finite list
and tests the exact rational-coordinate root predicate.  The factorized
specialization below fixes the polynomial to the one built from its supplied
factor list.  Thus the completeness statement is only relative to the
candidate list; it is not an arbitrary-polynomial existence theorem. -/

def exactRootSearch (coeffs : CPoly.Coeffs) : List QComplex -> Option QComplex
  | [] => none
  | z :: zs =>
      if CPoly.eval coeffs z = QComplex.zero then some z
      else exactRootSearch coeffs zs

def factorizedPolynomialRootSearch (roots candidates : List QComplex) :
    Option QComplex :=
  exactRootSearch (factorizedPolynomial roots) candidates

theorem exactRootSearch_sound
    {coeffs : CPoly.Coeffs} {candidates : List QComplex} {z : QComplex}
    (hsearch : exactRootSearch coeffs candidates = some z) :
    CPoly.hasExactRoot coeffs z := by
  induction candidates with
  | nil => simp [exactRootSearch] at hsearch
  | cons candidate candidates ih =>
      simp only [exactRootSearch] at hsearch
      split at hsearch
      · cases hsearch
        exact by assumption
      · exact ih hsearch

theorem exactRootSearch_complete
    {coeffs : CPoly.Coeffs} {candidates : List QComplex}
    (hexists : Exists fun z => z ∈ candidates /\ CPoly.hasExactRoot coeffs z) :
    Exists fun z => exactRootSearch coeffs candidates = some z /\
      CPoly.hasExactRoot coeffs z := by
  induction candidates with
  | nil =>
      rcases hexists with ⟨z, hz, _⟩
      cases hz
  | cons candidate candidates ih =>
      rcases hexists with ⟨z, hz, hroot⟩
      simp only [List.mem_cons] at hz
      by_cases hcandidate : CPoly.eval coeffs candidate = QComplex.zero
      · exact ⟨candidate, by simp [exactRootSearch, hcandidate], hcandidate⟩
      · simp only [exactRootSearch, hcandidate]
        exact ih ⟨z, hz.resolve_left (by
          intro hzc
          subst z
          exact hcandidate hroot), hroot⟩

theorem exactRootSearch_none_iff
    {coeffs : CPoly.Coeffs} {candidates : List QComplex} :
    exactRootSearch coeffs candidates = none ↔
      ∀ z, z ∈ candidates -> ¬ CPoly.hasExactRoot coeffs z := by
  induction candidates with
  | nil => simp [exactRootSearch]
  | cons candidate candidates ih =>
      by_cases hcandidate : CPoly.eval coeffs candidate = QComplex.zero
      · simp [exactRootSearch, hcandidate, CPoly.hasExactRoot]
      · simp only [exactRootSearch, hcandidate, ih, List.mem_cons]
        simp [CPoly.hasExactRoot, hcandidate, ih]

theorem factorizedPolynomialRootSearch_sound
    {roots candidates : List QComplex} {z : QComplex}
    (hsearch : factorizedPolynomialRootSearch roots candidates = some z) :
    CPoly.hasExactRoot (factorizedPolynomial roots) z := by
  exact exactRootSearch_sound hsearch

theorem factorizedPolynomialRootSearch_returns_supplied_root
    {roots candidates : List QComplex} {z : QComplex}
    (hsearch : factorizedPolynomialRootSearch roots candidates = some z) :
    z ∈ roots := by
  have hroot := factorizedPolynomialRootSearch_sound hsearch
  change CPoly.eval (factorizedPolynomial roots) z = QComplex.zero at hroot
  exact (factorizedPolynomial_eval_eq_zero_iff_mem).mp hroot

theorem factorizedPolynomialRootSearch_complete
    {roots candidates : List QComplex}
    (hexists : Exists fun z => z ∈ candidates /\
      CPoly.hasExactRoot (factorizedPolynomial roots) z) :
    Exists fun z => factorizedPolynomialRootSearch roots candidates = some z /\
      CPoly.hasExactRoot (factorizedPolynomial roots) z := by
  exact exactRootSearch_complete hexists

theorem factorizedPolynomialRootSearch_self_some
    {roots : List QComplex} (hroots : roots ≠ []) :
    Exists fun z =>
      factorizedPolynomialRootSearch roots roots = some z ∧ z ∈ roots := by
  cases roots with
  | nil => exact False.elim (hroots rfl)
  | cons r rs =>
      have hmem : r ∈ r :: rs := by simp
      have hroot : CPoly.hasExactRoot
          (factorizedPolynomial (r :: rs)) r :=
        factorizedPolynomial_exact_root_of_mem hmem
      rcases factorizedPolynomialRootSearch_complete
        (roots := r :: rs) (candidates := r :: rs)
        ⟨r, hmem, hroot⟩ with ⟨z, hz, _⟩
      exact ⟨z, hz, factorizedPolynomialRootSearch_returns_supplied_root hz⟩

theorem factorizedPolynomialRootSearch_none_iff
    {roots candidates : List QComplex} :
    factorizedPolynomialRootSearch roots candidates = none ↔
      ∀ z, z ∈ candidates -> z ∉ roots := by
  rw [show factorizedPolynomialRootSearch roots candidates =
      exactRootSearch (factorizedPolynomial roots) candidates by rfl,
    exactRootSearch_none_iff]
  simp [CPoly.hasExactRoot, factorizedPolynomial_eval_eq_zero_iff_mem]

theorem factorizedPolynomialRootSearch_complete_computable
    {roots candidates : List QComplex}
    (hexists : Exists fun z => z ∈ candidates /\
      CPoly.hasExactRoot (factorizedPolynomial roots) z) :
    Exists fun z =>
      factorizedPolynomialRootSearch roots candidates = some z /\
      IsComputableRoot (factorizedPolynomial roots) (exactComplexCert z) := by
  rcases factorizedPolynomialRootSearch_complete hexists with
    ⟨z, hsearch, hroot⟩
  exact ⟨z, hsearch, exactRoot_is_computable hroot⟩

theorem factorizedPolynomialRootSearch_self_some_computable
    {roots : List QComplex} (hroots : roots ≠ []) :
    Exists fun z =>
      factorizedPolynomialRootSearch roots roots = some z /\
        IsComputableRoot (factorizedPolynomial roots) (exactComplexCert z) := by
  cases roots with
  | nil => exact False.elim (hroots rfl)
  | cons r rs =>
      have hmem : r ∈ r :: rs := by simp
      have hroot : CPoly.hasExactRoot
          (factorizedPolynomial (r :: rs)) r :=
        factorizedPolynomial_exact_root_of_mem hmem
      exact factorizedPolynomialRootSearch_complete_computable
        ⟨r, hmem, hroot⟩

theorem factorizedPolynomialRootSearch_self_some_computable_mem
    {roots : List QComplex} (hroots : roots ≠ []) :
    Exists fun z =>
      factorizedPolynomialRootSearch roots roots = some z /\
        z ∈ roots /\
        IsComputableRoot (factorizedPolynomial roots) (exactComplexCert z) := by
  rcases factorizedPolynomialRootSearch_self_some_computable hroots with
    ⟨z, hsearch, hcomputable⟩
  exact ⟨z, hsearch,
    factorizedPolynomialRootSearch_returns_supplied_root hsearch, hcomputable⟩

theorem factorizedQuarticPolynomial_root_search_some_computable
    (r s t u : QComplex) :
    Exists fun z =>
      factorizedPolynomialRootSearch [r, s, t, u] [r, s, t, u] = some z /\
        z ∈ [r, s, t, u] /\
        IsComputableRoot (factorizedQuarticPolynomial r s t u)
          (exactComplexCert z) := by
  rcases factorizedPolynomialRootSearch_self_some_computable_mem
      (roots := [r, s, t, u]) (by simp) with
    ⟨z, hsearch, hmem, _⟩
  refine ⟨z, hsearch, hmem, ?_⟩
  apply exactRoot_is_computable
  apply (factorizedQuarticPolynomial_hasExactRoot_iff r s t u z).2
  simpa using hmem

theorem factorizedCubicPolynomial_root_search_some_computable
    (r s t : QComplex) :
    Exists fun z =>
      factorizedPolynomialRootSearch [r, s, t] [r, s, t] = some z /\
        z ∈ [r, s, t] /\
        IsComputableRoot (factorizedCubicPolynomial r s t)
          (exactComplexCert z) := by
  rcases factorizedPolynomialRootSearch_self_some_computable_mem
      (roots := [r, s, t]) (by simp) with
    ⟨z, hsearch, hmem, _⟩
  refine ⟨z, hsearch, hmem, ?_⟩
  apply exactRoot_is_computable
  apply (factorizedCubicPolynomial_hasExactRoot_iff r s t z).2
  simpa using hmem

theorem factorizedPolynomialRootSearch_returns_computable_root
    {roots candidates : List QComplex} {z : QComplex}
    (hsearch : factorizedPolynomialRootSearch roots candidates = some z) :
    IsComputableRoot (factorizedPolynomial roots) (exactComplexCert z) := by
  exact exactRoot_is_computable (factorizedPolynomialRootSearch_sound hsearch)

/-! A named finite quintic factorization boundary.

This packages the generic list construction at exactly five supplied roots.  The
result is an explicit rational-coordinate quintic certificate; it does not
assert that an arbitrary quintic has such a factorization, and it makes no
claim about a general quintic formula or Abel--Ruffini. -/

def factorizedQuinticPolynomial (r₁ r₂ r₃ r₄ r₅ : QComplex) : CPoly.Coeffs :=
  factorizedPolynomial [r₁, r₂, r₃, r₄, r₅]

theorem factorizedQuinticPolynomial_eval_eq_product
    (r₁ r₂ r₃ r₄ r₅ z : QComplex) :
    CPoly.eval (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅) z =
      QComplex.mul (QComplex.sub z r₁)
      (QComplex.mul (QComplex.sub z r₂)
          (QComplex.mul (QComplex.sub z r₃)
            (QComplex.mul (QComplex.sub z r₄)
              (QComplex.sub z r₅)))) := by
  change CPoly.eval (factorizedPolynomial [r₁, r₂, r₃, r₄, r₅]) z = _
  rw [factorizedPolynomial_eval_eq_product]
  simp only [List.foldr]
  have hone (w : QComplex) : QComplex.mul w QComplex.one = w := by
    cases w with
    | mk re im =>
        simp [QComplex.mul, QComplex.one]
        grind
  rw [hone]

theorem factorizedQuinticPolynomial_eval_eq_zero_iff
    (r₁ r₂ r₃ r₄ r₅ z : QComplex) :
    CPoly.eval (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅) z = QComplex.zero ↔
      z = r₁ ∨ z = r₂ ∨ z = r₃ ∨ z = r₄ ∨ z = r₅ := by
  have hsub : ∀ x y : QComplex,
      QComplex.sub x y = QComplex.zero ↔ x = y := by
    intro x y
    cases x
    cases y
    simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
    grind [Rat.sub_eq_add_neg]
  rw [factorizedQuinticPolynomial_eval_eq_product]
  constructor
  · intro h
    rcases QComplex.mul_eq_zero.mp h with hfirst | hrest
    · exact Or.inl (hsub z r₁ |>.mp hfirst)
    · rcases QComplex.mul_eq_zero.mp hrest with hsecond | hrest
      · exact Or.inr (Or.inl (hsub z r₂ |>.mp hsecond))
      · rcases QComplex.mul_eq_zero.mp hrest with hthird | hrest
        · exact Or.inr (Or.inr (Or.inl (hsub z r₃ |>.mp hthird)))
        · rcases QComplex.mul_eq_zero.mp hrest with hfourth | hfifth
          · exact Or.inr (Or.inr (Or.inr (Or.inl (hsub z r₄ |>.mp hfourth))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (hsub z r₅ |>.mp hfifth))))
  · intro h
    rcases h with h | h | h | h | h
    · have hz : QComplex.sub z r₁ = QComplex.zero := (hsub z r₁).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z r₂ = QComplex.zero := (hsub z r₂).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z r₃ = QComplex.zero := (hsub z r₃).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z r₄ = QComplex.zero := (hsub z r₄).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind
    · have hz : QComplex.sub z r₅ = QComplex.zero := (hsub z r₅).2 h
      rw [hz]
      simp [QComplex.mul, QComplex.zero]
      grind

theorem factorizedQuinticPolynomial_eval_eq_zero_iff_mem
    (r₁ r₂ r₃ r₄ r₅ z : QComplex) :
    CPoly.eval (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅) z = QComplex.zero ↔
      z ∈ [r₁, r₂, r₃, r₄, r₅] := by
  rw [factorizedQuinticPolynomial_eval_eq_zero_iff]
  simp

theorem factorizedQuinticPolynomial_hasExactRoot_iff_mem
    (r₁ r₂ r₃ r₄ r₅ r : QComplex) :
    CPoly.hasExactRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅) r ↔
      r ∈ [r₁, r₂, r₃, r₄, r₅] := by
  change CPoly.eval (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅) r =
    QComplex.zero ↔ _
  exact factorizedQuinticPolynomial_eval_eq_zero_iff_mem r₁ r₂ r₃ r₄ r₅ r

theorem factorizedQuinticPolynomial_exact_root_of_mem
    {r₁ r₂ r₃ r₄ r₅ r : QComplex}
    (hr : r ∈ [r₁, r₂, r₃, r₄, r₅]) :
    CPoly.hasExactRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅) r := by
  exact factorizedPolynomial_exact_root_of_mem hr

theorem factorizedQuinticPolynomial_computable_root_of_mem
    {r₁ r₂ r₃ r₄ r₅ r : QComplex}
    (hr : r ∈ [r₁, r₂, r₃, r₄, r₅]) :
    IsComputableRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅)
      (exactComplexCert r) := by
  exact factorizedPolynomial_computable_root_of_mem hr

/-- A direct existence package for the finite quintic factorization.  The
first supplied factor is an explicit computable root; no general quintic
root solver is being asserted. -/
theorem factorizedQuinticPolynomial_has_computable_root
    (r₁ r₂ r₃ r₄ r₅ : QComplex) :
    Exists fun z : ComplexCert =>
      IsComputableRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅) z := by
  refine ⟨exactComplexCert r₁, ?_⟩
  exact factorizedQuinticPolynomial_computable_root_of_mem (by simp)

theorem factorizedQuinticPolynomial_has_all_computable_roots
    (r₁ r₂ r₃ r₄ r₅ : QComplex) :
    IsComputableRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅)
        (exactComplexCert r₁) ∧
      IsComputableRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅)
        (exactComplexCert r₂) ∧
      IsComputableRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅)
        (exactComplexCert r₃) ∧
      IsComputableRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅)
        (exactComplexCert r₄) ∧
      IsComputableRoot (factorizedQuinticPolynomial r₁ r₂ r₃ r₄ r₅)
        (exactComplexCert r₅) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact factorizedQuinticPolynomial_computable_root_of_mem (by simp)
  · exact factorizedQuinticPolynomial_computable_root_of_mem (by simp)
  · exact factorizedQuinticPolynomial_computable_root_of_mem (by simp)
  · exact factorizedQuinticPolynomial_computable_root_of_mem (by simp)
  · exact factorizedQuinticPolynomial_computable_root_of_mem (by simp)

abbrev imaginaryUnit : QComplex := RootsOfUnity.imaginaryUnitQ

def zSqPlusOne : CPoly.Coeffs := [QComplex.one, QComplex.zero, QComplex.one]

theorem zSqPlusOne_i_exact_root :
    CPoly.hasExactRoot zSqPlusOne imaginaryUnit := by
  simp [CPoly.hasExactRoot, zSqPlusOne, imaginaryUnit,
    RootsOfUnity.imaginaryUnitQ, CPoly.eval, QComplex.add, QComplex.mul,
    QComplex.one, QComplex.zero]
  grind [Rat.sub_eq_add_neg]

theorem zSqPlusOne_has_computable_root :
    Exists fun z : ComplexCert => IsComputableRoot zSqPlusOne z := by
  refine Exists.intro RootsOfUnity.imaginaryUnit.number.value ?_
  exact exactRoot_is_computable zSqPlusOne_i_exact_root

theorem zSqPlusOne_has_algebraic_root :
    Exists fun z : AlgebraicComplex => IsAlgebraicRoot zSqPlusOne z := by
  refine Exists.intro RootsOfUnity.imaginaryUnit.number ?_
  exact exactRoot_is_computable zSqPlusOne_i_exact_root

/-- Constructive/computable form of the Fundamental Theorem of Algebra target. -/
def ComputableFTA : Prop :=
  forall coeffs : CPoly.Coeffs,
    CPoly.positiveDegree coeffs ->
      Exists fun z : ComplexCert => IsComputableRoot coeffs z

/-- Algebraic-number form of FTA for rational-complex coefficient polynomials.

This is the sharper target for this project: the root is not just computable,
but packaged as an algebraic complex number with its own rational annihilator.
-/
def AlgebraicFTA : Prop :=
  forall coeffs : CPoly.Coeffs,
    CPoly.positiveDegree coeffs ->
      Exists fun z : AlgebraicComplex => IsAlgebraicRoot coeffs z

/-! A factorization witness is enough to close the project-facing FTA target.
The theorem below deliberately leaves the global existence of such a witness
as a separate assumption: the computational content is the finite extraction
of one supplied factor and its exact algebraic certificate. -/

theorem AlgebraicFTA_of_factorizedWitness
    (hfactor : forall coeffs : CPoly.Coeffs,
      CPoly.positiveDegree coeffs ->
        Exists fun roots : List QComplex =>
          roots ≠ [] ∧ coeffs = factorizedPolynomial roots) :
    AlgebraicFTA := by
  intro coeffs hdegree
  rcases hfactor coeffs hdegree with ⟨roots, hroots, hcoeffs⟩
  cases roots with
  | nil => exact False.elim (hroots rfl)
  | cons r rs =>
      refine ⟨AlgebraicComplex.ofQComplex r, ?_⟩
      rw [hcoeffs]
      exact exactRoot_is_computable
        (factorizedPolynomial_exact_root_of_mem (by simp))

theorem ComputableFTA_of_AlgebraicFTA :
    AlgebraicFTA -> ComputableFTA := by
  intro h coeffs hp
  rcases h coeffs hp with ⟨z, hz⟩
  exact ⟨z.value, hz⟩

end ComputableAnalysis
