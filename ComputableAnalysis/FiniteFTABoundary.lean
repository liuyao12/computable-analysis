import ComputableAnalysis.ComplexPolynomial

/-!
# A finite FTA boundary certificate: one-step complex deflation

The existing FTA files construct polynomials from a supplied list of factors.
This module goes in the other direction.  Given an arbitrary finite
rational-complex coefficient list and a supplied exact root, `syntheticDivide`
computes the next coefficient list and proves the exact remainder identity.

This is a certificate interface for root peeling, not a root-existence theorem:
the root is input data, and no claim of algebraic closure or global FTA is made.
-/

namespace ComputableAnalysis

namespace FiniteFTABoundary

private theorem qcomplex_add_assoc (z w u : QComplex) :
    QComplex.add (QComplex.add z w) u = QComplex.add z (QComplex.add w u) := by
  cases z
  cases w
  cases u
  simp [QComplex.add]
  grind [Rat.add_assoc]

private theorem qcomplex_add_comm (z w : QComplex) :
    QComplex.add z w = QComplex.add w z := by
  cases z
  cases w
  simp [QComplex.add]
  grind [Rat.add_comm]

private theorem qcomplex_add_zero (z : QComplex) :
    QComplex.add z QComplex.zero = z := by
  cases z
  simp [QComplex.add, QComplex.zero]
  grind

private theorem qcomplex_mul_assoc (z w u : QComplex) :
    QComplex.mul (QComplex.mul z w) u =
      QComplex.mul z (QComplex.mul w u) := by
  cases z
  cases w
  cases u
  simp [QComplex.mul]
  congr 1 <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.sub_eq_add_neg]

private theorem qcomplex_mul_comm (z w : QComplex) :
    QComplex.mul z w = QComplex.mul w z := by
  cases z
  cases w
  simp [QComplex.mul]
  congr 1 <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_comm,
    Rat.sub_eq_add_neg]

private theorem qcomplex_mul_add (z w u : QComplex) :
    QComplex.mul z (QComplex.add w u) =
      QComplex.add (QComplex.mul z w) (QComplex.mul z u) := by
  cases z
  cases w
  cases u
  simp [QComplex.mul, QComplex.add]
  congr 1 <;> grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
    Rat.sub_eq_add_neg]

private theorem qcomplex_add_mul (z w u : QComplex) :
    QComplex.mul (QComplex.add z w) u =
      QComplex.add (QComplex.mul z u) (QComplex.mul w u) := by
  rw [qcomplex_mul_comm, qcomplex_mul_add]
  congr 1 <;> exact qcomplex_mul_comm _ _

private theorem qcomplex_sub_eq_add_neg (z w : QComplex) :
    QComplex.sub z w = QComplex.add z (QComplex.neg w) := rfl

private theorem qcomplex_sub_self (z : QComplex) :
    QComplex.sub z z = QComplex.zero := by
  cases z
  simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
  constructor <;> grind

private theorem qcomplex_mul_zero (z : QComplex) :
    QComplex.mul z QComplex.zero = QComplex.zero := by
  cases z
  simp [QComplex.mul, QComplex.zero]
  constructor <;> grind

private theorem qcomplex_zero_mul (z : QComplex) :
    QComplex.mul QComplex.zero z = QComplex.zero := by
  cases z
  simp [QComplex.mul, QComplex.zero]
  grind

private theorem qcomplex_zero_add (z : QComplex) :
    QComplex.add QComplex.zero z = z := by
  rw [qcomplex_add_comm, qcomplex_add_zero]

private theorem qcomplex_deflation_step (c root x b q : QComplex) :
    QComplex.add c
        (QComplex.mul x
          (QComplex.add b (QComplex.mul (QComplex.sub x root) q))) =
      QComplex.add (QComplex.add c (QComplex.mul root b))
        (QComplex.mul (QComplex.sub x root)
          (QComplex.add b (QComplex.mul x q))) := by
  cases c
  cases root
  cases x
  cases b
  cases q
  simp [QComplex.add, QComplex.mul, QComplex.sub, QComplex.neg]
  grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm, Rat.mul_add,
    Rat.add_mul, Rat.mul_assoc, Rat.mul_comm, Rat.sub_eq_add_neg,
    Rat.neg_mul, Rat.mul_neg]

/-! The quotient is stored in the same constant-first Horner convention as
`CPoly.eval`. -/

def syntheticDivide (root : QComplex) : CPoly.Coeffs -> CPoly.Coeffs × QComplex
  | [] => ([], QComplex.zero)
  | c :: cs =>
      let qr := syntheticDivide root cs
      (qr.2 :: qr.1, QComplex.add c (QComplex.mul root qr.2))

/-- Synthetic division preserves the constant-first coefficient count in its
quotient slot: the padded quotient has one entry per input coefficient. -/
theorem syntheticDivide_quotient_length (root : QComplex)
    (coeffs : CPoly.Coeffs) :
    (syntheticDivide root coeffs).1.length = coeffs.length := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
      simp [syntheticDivide, ih]

/-- For every nonempty input, synthetic division returns a quotient whose
last entry is the padding zero; trimming that entry lowers the coefficient
count by one. -/
theorem syntheticDivide_quotient_padded
    (root : QComplex) {coeffs : CPoly.Coeffs} (hcoeffs : coeffs ≠ []) :
    ∃ qs : CPoly.Coeffs,
      (syntheticDivide root coeffs).1 = qs ++ [QComplex.zero] ∧
        qs.length + 1 = coeffs.length := by
  induction coeffs with
  | nil => exact False.elim (hcoeffs rfl)
  | cons c cs ih =>
      cases cs with
      | nil =>
          refine ⟨[], ?_, ?_⟩
          · simp [syntheticDivide]
          · simp
      | cons d ds =>
          have hnonempty : d :: ds ≠ [] := by simp
          obtain ⟨qs, hqs, hlen⟩ := ih (by simp)
          refine ⟨(syntheticDivide root (d :: ds)).2 :: qs, ?_, ?_⟩
          · change
              (syntheticDivide root (d :: ds)).2 ::
                  (syntheticDivide root (d :: ds)).1 =
                ((syntheticDivide root (d :: ds)).2 :: qs) ++ [QComplex.zero]
            rw [hqs]
            simp [List.cons_append]
          · simp [syntheticDivide, hlen]

private theorem cpoly_eval_cons (c : QComplex) (p : CPoly.Coeffs) (z : QComplex) :
    CPoly.eval (c :: p) z =
      QComplex.add c (QComplex.mul z (CPoly.eval p z)) := rfl

theorem syntheticDivide_spec (root x : QComplex) (coeffs : CPoly.Coeffs) :
    let qr := syntheticDivide root coeffs
    CPoly.eval coeffs x =
      QComplex.add qr.2
        (QComplex.mul (QComplex.sub x root) (CPoly.eval qr.1 x)) := by
  induction coeffs with
  | nil =>
      simp [syntheticDivide, CPoly.eval, QComplex.zero, QComplex.add,
        QComplex.mul]
      grind
  | cons c cs ih =>
      let qr := syntheticDivide root cs
      have hih : CPoly.eval cs x =
          QComplex.add qr.2
            (QComplex.mul (QComplex.sub x root) (CPoly.eval qr.1 x)) := by
        simpa [qr] using ih
      change QComplex.add c (QComplex.mul x (CPoly.eval cs x)) =
        QComplex.add (QComplex.add c (QComplex.mul root qr.2))
          (QComplex.mul (QComplex.sub x root)
            (CPoly.eval (qr.2 :: qr.1) x))
      rw [hih]
      rw [cpoly_eval_cons]
      exact qcomplex_deflation_step c root x qr.2 (CPoly.eval qr.1 x)

theorem syntheticDivide_remainder_eq_eval (root : QComplex)
    (coeffs : CPoly.Coeffs) :
    (syntheticDivide root coeffs).2 = CPoly.eval coeffs root := by
  have h := syntheticDivide_spec root root coeffs
  dsimp at h
  rw [qcomplex_sub_self, qcomplex_zero_mul, qcomplex_add_zero] at h
  exact h.symm

theorem syntheticDivide_remainder_eq_zero_iff (root : QComplex)
    (coeffs : CPoly.Coeffs) :
    (syntheticDivide root coeffs).2 = QComplex.zero ↔
      CPoly.hasExactRoot coeffs root := by
  rw [syntheticDivide_remainder_eq_eval]
  rfl

theorem syntheticDivide_factor_of_root
    {root x : QComplex} {coeffs : CPoly.Coeffs}
    (hroot : CPoly.hasExactRoot coeffs root) :
    CPoly.eval coeffs x =
      QComplex.mul (QComplex.sub x root)
        (CPoly.eval (syntheticDivide root coeffs).1 x) := by
  have h := syntheticDivide_spec root x coeffs
  dsimp at h
  rw [syntheticDivide_remainder_eq_eval] at h
  rw [hroot] at h
  rw [qcomplex_zero_add] at h
  exact h

structure DeflationCertificate (coeffs : CPoly.Coeffs) (root : QComplex) where
  quotient : CPoly.Coeffs
  remainder : QComplex
  factor_remainder : ∀ x : QComplex,
    CPoly.eval coeffs x =
      QComplex.add remainder
        (QComplex.mul (QComplex.sub x root) (CPoly.eval quotient x))
  remainder_value : remainder = CPoly.eval coeffs root

def syntheticDeflationCertificate (coeffs : CPoly.Coeffs) (root : QComplex) :
    DeflationCertificate coeffs root where
  quotient := (syntheticDivide root coeffs).1
  remainder := (syntheticDivide root coeffs).2
  factor_remainder x := by
    simpa using syntheticDivide_spec root x coeffs
  remainder_value := syntheticDivide_remainder_eq_eval root coeffs

theorem DeflationCertificate.factor_at
    {coeffs : CPoly.Coeffs} {root x : QComplex}
    (certificate : DeflationCertificate coeffs root) :
    CPoly.eval coeffs x =
      QComplex.add certificate.remainder
        (QComplex.mul (QComplex.sub x root)
          (CPoly.eval certificate.quotient x)) := by
  exact certificate.factor_remainder x

theorem DeflationCertificate.factor_of_root
    {coeffs : CPoly.Coeffs} {root x : QComplex}
    (certificate : DeflationCertificate coeffs root)
    (hroot : CPoly.hasExactRoot coeffs root) :
    CPoly.eval coeffs x =
      QComplex.mul (QComplex.sub x root)
        (CPoly.eval certificate.quotient x) := by
  rw [certificate.factor_remainder x, certificate.remainder_value, hroot]
  rw [qcomplex_zero_add]

theorem syntheticDeflationCertificate_factor_of_root
    {coeffs : CPoly.Coeffs} {root x : QComplex}
    (hroot : CPoly.hasExactRoot coeffs root) :
    CPoly.eval coeffs x =
      QComplex.mul (QComplex.sub x root)
        (CPoly.eval (syntheticDivide root coeffs).1 x) := by
  exact syntheticDivide_factor_of_root hroot

end FiniteFTABoundary

end ComputableAnalysis
