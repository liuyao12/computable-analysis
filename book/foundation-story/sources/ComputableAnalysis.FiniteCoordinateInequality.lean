import ComputableAnalysis.Basic

/-!
# Finite coordinate Cauchy--Schwarz certificates

The two-dimensional rational Cauchy--Schwarz inequality is proved by the
explicit Lagrange identity.  The remainder is the square
`(a*d-b*c)^2`, so the proof stays entirely inside finite rational arithmetic.
The `QComplex` corollary supplies the dot-product bound used by squared-norm
triangle estimates.
-/

namespace ComputableAnalysis

theorem rational_coordinate_cauchy_schwarz (a b c d : Rat) :
    (a * c + b * d) ^ 2 <=
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have hsq : 0 <= (a * d - b * c) ^ 2 :=
    by simpa [Rat.pow_succ] using rat_square_nonneg_basic (a * d - b * c)
  have hid :
      (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) -
          (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by
    grind [Rat.pow_succ, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  rw [show (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) =
      (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 by grind]
  grind

theorem qcomplex_coordinate_cauchy_schwarz (z w : QComplex) :
    (z.re * w.re + z.im * w.im) ^ 2 <=
      QComplex.normSq z * QComplex.normSq w := by
  simpa [QComplex.normSq, Rat.pow_succ] using
    rational_coordinate_cauchy_schwarz z.re z.im w.re w.im

theorem qcomplex_normSq_add_expansion (z w : QComplex) :
    QComplex.normSq (QComplex.add z w) =
      QComplex.normSq z + QComplex.normSq w +
        2 * (z.re * w.re + z.im * w.im) := by
  cases z
  cases w
  simp [QComplex.normSq, QComplex.add]
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem qcomplex_normSq_add_le_coordinate_abs (z w : QComplex) :
    QComplex.normSq (QComplex.add z w) ≤
      (qabs z.re + qabs w.re) ^ 2 +
        (qabs z.im + qabs w.im) ^ 2 := by
  have square_abs (x : Rat) : x ^ 2 = (qabs x) ^ 2 := by
    calc
      x ^ 2 = x * x := by simpa [Rat.pow_succ]
      _ = qabs (x * x) := by
        symm
        exact qabs_eq_self_of_nonneg (rat_square_nonneg_basic x)
      _ = qabs x * qabs x := qabs_mul x x
      _ = (qabs x) ^ 2 := by simpa [Rat.pow_succ]
  have square_mono {x y : Rat} (hxy : qabs x ≤ y) (hy : 0 ≤ y) :
      x ^ 2 ≤ y ^ 2 := by
    rw [square_abs]
    have hleft := Rat.mul_le_mul_of_nonneg_right hxy (qabs_nonneg x)
    have hright := Rat.mul_le_mul_of_nonneg_left hxy hy
    calc
      qabs x ^ 2 = qabs x * qabs x := by simpa [Rat.pow_succ]
      _ ≤ y * qabs x := hleft
      _ ≤ y * y := hright
      _ = y ^ 2 := by simpa [Rat.pow_succ]
  have hre : qabs (z.re + w.re) ≤ qabs z.re + qabs w.re :=
    qabs_add_le z.re w.re
  have him : qabs (z.im + w.im) ≤ qabs z.im + qabs w.im :=
    qabs_add_le z.im w.im
  have hre_sq : (z.re + w.re) ^ 2 ≤
      (qabs z.re + qabs w.re) ^ 2 :=
    square_mono hre (Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _))
  have him_sq : (z.im + w.im) ^ 2 ≤
      (qabs z.im + qabs w.im) ^ 2 :=
    square_mono him (Rat.add_nonneg (qabs_nonneg _) (qabs_nonneg _))
  simpa [QComplex.normSq, QComplex.add, Rat.pow_succ] using
    rat_add_le_add hre_sq him_sq

end ComputableAnalysis
