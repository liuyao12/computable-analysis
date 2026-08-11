import ComputableAnalysis.FTA

namespace ComputableAnalysis

/-!
# Finite quartics split into two supplied quadratics

This module records a finite factorized quartic certificate.  The coefficient
list is constant-first, and every factor and root used below is supplied by
the caller.
-/

/-- The constant-first coefficient list of
`qcomplexQuadraticPolynomial a b c * qcomplexQuadraticPolynomial d e f`. -/
def finiteQuarticQuadraticSplit
    (a b c d e f : QComplex) : CPoly.Coeffs :=
  [QComplex.mul c f,
    QComplex.add (QComplex.mul b f) (QComplex.mul c e),
    QComplex.add
      (QComplex.add (QComplex.mul a f) (QComplex.mul b e))
        (QComplex.mul c d),
    QComplex.add (QComplex.mul a e) (QComplex.mul b d),
    QComplex.mul a d]

/-- Horner evaluation of the finite quartic is the product of its two
quadratic evaluations. -/
theorem finiteQuarticQuadraticSplit_eval
    (a b c d e f z : QComplex) :
    CPoly.eval (finiteQuarticQuadraticSplit a b c d e f) z =
      QComplex.mul
        (CPoly.eval (qcomplexQuadraticPolynomial a b c) z)
        (CPoly.eval (qcomplexQuadraticPolynomial d e f) z) := by
  simp [finiteQuarticQuadraticSplit, qcomplexQuadraticPolynomial,
    CPoly.eval, QComplex.add, QComplex.mul, QComplex.zero]
  cases a with
  | mk ar ai =>
    cases b with
    | mk br bi =>
      cases c with
      | mk cr ci =>
        cases d with
        | mk dr di =>
          cases e with
          | mk er ei =>
            cases f with
            | mk fr fi =>
              cases z with
              | mk zr zi =>
                simp
                grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
                  Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm,
                  Rat.add_left_comm]

/-- Supplied exact roots of either quadratic factor are exact roots of the
finite quartic split.  No root existence or completeness claim is made. -/
theorem finiteQuarticQuadraticSplit_hasExactRoots
    (a b c d e f r₁ r₂ s₁ s₂ : QComplex)
    (hr₁ : CPoly.hasExactRoot (qcomplexQuadraticPolynomial a b c) r₁)
    (hr₂ : CPoly.hasExactRoot (qcomplexQuadraticPolynomial a b c) r₂)
    (hs₁ : CPoly.hasExactRoot (qcomplexQuadraticPolynomial d e f) s₁)
    (hs₂ : CPoly.hasExactRoot (qcomplexQuadraticPolynomial d e f) s₂) :
    CPoly.hasExactRoot (finiteQuarticQuadraticSplit a b c d e f) r₁ ∧
    CPoly.hasExactRoot (finiteQuarticQuadraticSplit a b c d e f) r₂ ∧
    CPoly.hasExactRoot (finiteQuarticQuadraticSplit a b c d e f) s₁ ∧
    CPoly.hasExactRoot (finiteQuarticQuadraticSplit a b c d e f) s₂ := by
  constructor
  · change CPoly.eval (finiteQuarticQuadraticSplit a b c d e f) r₁ =
      QComplex.zero
    rw [finiteQuarticQuadraticSplit_eval, hr₁]
    simp [QComplex.mul, QComplex.zero]
    constructor <;> grind
  constructor
  · change CPoly.eval (finiteQuarticQuadraticSplit a b c d e f) r₂ =
      QComplex.zero
    rw [finiteQuarticQuadraticSplit_eval, hr₂]
    simp [QComplex.mul, QComplex.zero]
    constructor <;> grind
  constructor
  · change CPoly.eval (finiteQuarticQuadraticSplit a b c d e f) s₁ =
      QComplex.zero
    rw [finiteQuarticQuadraticSplit_eval, hs₁]
    simp [QComplex.mul, QComplex.zero]
    constructor <;> grind
  · change CPoly.eval (finiteQuarticQuadraticSplit a b c d e f) s₂ =
      QComplex.zero
    rw [finiteQuarticQuadraticSplit_eval, hs₂]
    simp [QComplex.mul, QComplex.zero]
    constructor <;> grind

end ComputableAnalysis
