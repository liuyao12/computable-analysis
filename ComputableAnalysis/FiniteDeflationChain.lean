import ComputableAnalysis.FiniteFTABoundary

/-!
# Finite deflation chains over supplied rational-complex roots

This module iterates the one-step certificate from `FiniteFTABoundary`.  The
roots are input data: `IsDeflationChain` asks for an exact root at each stage,
and makes no root-existence, algebraic-closure, or global FTA assertion.
-/

namespace ComputableAnalysis

namespace FiniteDeflationChain

open FiniteFTABoundary

def deflatedCoeffs : CPoly.Coeffs → List QComplex → CPoly.Coeffs
  | coeffs, [] => coeffs
  | coeffs, root :: roots =>
      deflatedCoeffs (syntheticDivide root coeffs).1 roots

def IsDeflationChain (coeffs : CPoly.Coeffs) : List QComplex → Prop
  | [] => True
  | root :: roots =>
      CPoly.hasExactRoot coeffs root ∧
        IsDeflationChain (syntheticDivide root coeffs).1 roots

def rootFactorProduct : List QComplex → QComplex → QComplex
  | [], _ => QComplex.one
  | root :: roots, x =>
      QComplex.mul (QComplex.sub x root) (rootFactorProduct roots x)

private theorem qcomplex_mul_assoc (z w u : QComplex) :
    QComplex.mul (QComplex.mul z w) u =
      QComplex.mul z (QComplex.mul w u) := by
  cases z
  cases w
  cases u
  simp [QComplex.mul]
  congr 1 <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.sub_eq_add_neg]

private theorem qcomplex_mul_one (z : QComplex) :
    QComplex.mul z QComplex.one = z := by
  cases z
  simp [QComplex.mul, QComplex.one]
  constructor <;> grind

private theorem qcomplex_one_mul (z : QComplex) :
    QComplex.mul QComplex.one z = z := by
  cases z
  simp [QComplex.mul, QComplex.one]
  constructor <;> grind

theorem deflatedCoeffs_nil (coeffs : CPoly.Coeffs) :
    deflatedCoeffs coeffs [] = coeffs := rfl

theorem deflatedCoeffs_cons (coeffs : CPoly.Coeffs) (root : QComplex)
    (roots : List QComplex) :
    deflatedCoeffs coeffs (root :: roots) =
      deflatedCoeffs (syntheticDivide root coeffs).1 roots := rfl

/-- Each supplied-root deflation preserves the padded coefficient-list length.

The quotient representation deliberately carries one trailing zero, so this
is a finite shape invariant rather than a claim that a classical degree has
been reduced.  Any degree-decreasing interpretation must first remove that
padding explicitly. -/
theorem deflatedCoeffs_length (coeffs : CPoly.Coeffs)
    (roots : List QComplex) :
    (deflatedCoeffs coeffs roots).length = coeffs.length := by
  induction roots generalizing coeffs with
  | nil => rfl
  | cons root roots ih =>
      rw [deflatedCoeffs_cons, ih]
      exact syntheticDivide_quotient_length root coeffs

theorem isDeflationChain_nil (coeffs : CPoly.Coeffs) :
    IsDeflationChain coeffs [] := by
  trivial

theorem isDeflationChain_cons_iff (coeffs : CPoly.Coeffs) (root : QComplex)
    (roots : List QComplex) :
    IsDeflationChain coeffs (root :: roots) ↔
      CPoly.hasExactRoot coeffs root ∧
        IsDeflationChain (syntheticDivide root coeffs).1 roots := by
  rfl

theorem rootFactorProduct_nil (x : QComplex) :
    rootFactorProduct [] x = QComplex.one := rfl

theorem rootFactorProduct_cons (root : QComplex) (roots : List QComplex)
    (x : QComplex) :
    rootFactorProduct (root :: roots) x =
      QComplex.mul (QComplex.sub x root) (rootFactorProduct roots x) := rfl

theorem horner_factorization (coeffs : CPoly.Coeffs)
    (roots : List QComplex) (x : QComplex)
    (hchain : IsDeflationChain coeffs roots) :
    CPoly.eval coeffs x =
      QComplex.mul (rootFactorProduct roots x)
        (CPoly.eval (deflatedCoeffs coeffs roots) x) := by
  induction roots generalizing coeffs with
  | nil =>
      simp only [deflatedCoeffs, rootFactorProduct]
      exact (qcomplex_one_mul _).symm
  | cons root roots ih =>
      have hroot : CPoly.hasExactRoot coeffs root := hchain.1
      have htail : IsDeflationChain (syntheticDivide root coeffs).1 roots :=
        hchain.2
      have hstep := syntheticDivide_factor_of_root (x := x) hroot
      have hrest := ih (coeffs := (syntheticDivide root coeffs).1) htail
      rw [hstep, hrest]
      simp only [rootFactorProduct, deflatedCoeffs]
      exact (qcomplex_mul_assoc _ _ _).symm

end FiniteDeflationChain

end ComputableAnalysis
