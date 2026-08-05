import ComputableAnalysis.RotationPeanoBakerBridge
import ComputableAnalysis.RationalCircle

/-!
# The rational circle chart as a rotation equation

The rational circle chart
`t ↦ ((1 - t²)/(1 + t²), 2t/(1 + t²))` has a fully rational velocity.
Written as a rational complex point `z(t)`, its formal velocity is

`z'(t) = (2 i / (1 + t²)) z(t)`.

This file records the exact finite algebraic identity.  It is deliberately
not yet a theorem about a represented function or an ODE solution: the next
step is to give rational difference-quotient boxes and invoke the
Peano--Baker/Volterra uniqueness interface.  Keeping this part separate makes
the missing analytic bridge visible rather than silently treating the chart
parameter as an angle.
-/

namespace ComputableAnalysis

namespace GeometricRotationODE

/-- The rational circle point in complex-coordinate form. -/
def pointComplex (t : Rat) : QComplex :=
  { re := (RationalCircle.Stage.point t).x,
    im := (RationalCircle.Stage.point t).y }

/-- The exact rational velocity of the projective circle chart. -/
def pointComplexDerivative (t : Rat) : QComplex :=
  { re := (RationalCircle.Stage.pointDerivative t).x,
    im := (RationalCircle.Stage.pointDerivative t).y }

/-- The imaginary scalar which converts the chart parameter to angular time. -/
def angularVelocity (t : Rat) : QComplex :=
  { re := 0, im := 2 / (1 + t * t) }

/-- The two rational coordinate functions of the chart, named separately for
the finite-difference certificates below. -/
def pointRe (t : Rat) : Rat := (RationalCircle.Stage.point t).x
def pointIm (t : Rat) : Rat := (RationalCircle.Stage.point t).y

/-- Their exact rational derivative formulas. -/
def pointReDerivative (t : Rat) : Rat := (RationalCircle.Stage.pointDerivative t).x
def pointImDerivative (t : Rat) : Rat := (RationalCircle.Stage.pointDerivative t).y

theorem pointComplex_zero : pointComplex 0 = QComplex.one := by
  native_decide

theorem pointComplex_one : pointComplex 1 = RotationSeries.imaginaryUnit := by
  native_decide

/-- The real coordinate's finite difference quotient.  This is exact for
every nonzero rational step, before any small-step estimate is applied. -/
theorem pointRe_differenceQuotient (t h : Rat) (hh : h ≠ 0) :
    (pointRe (t + h) - pointRe t) / h =
      (-2 * (2 * t + h)) /
        ((1 + t * t) * (1 + (t + h) * (t + h))) := by
  unfold pointRe RationalCircle.Stage.point
  dsimp
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The imaginary coordinate's finite difference quotient. -/
theorem pointIm_differenceQuotient (t h : Rat) (hh : h ≠ 0) :
    (pointIm (t + h) - pointIm t) / h =
      (2 * (1 - t * t - t * h)) /
        ((1 + t * t) * (1 + (t + h) * (t + h))) := by
  unfold pointIm RationalCircle.Stage.point
  dsimp
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Exact real-coordinate secant error relative to the rational derivative.
The displayed factor of `h` is the finite source of the derivative modulus. -/
theorem pointRe_differenceQuotient_sub_derivative (t h : Rat) (hh : h ≠ 0) :
    (pointRe (t + h) - pointRe t) / h - pointReDerivative t =
      (2 * h * (-1 + 3 * t * t + 2 * t * h)) /
        ((1 + t * t) * (1 + t * t) * (1 + (t + h) * (t + h))) := by
  rw [pointRe_differenceQuotient t h hh]
  unfold pointReDerivative RationalCircle.Stage.pointDerivative
  dsimp
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  simp only [Rat.inv_mul_rev]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.neg_mul, Rat.mul_neg]

/-- Exact imaginary-coordinate secant error relative to the rational
derivative. -/
theorem pointIm_differenceQuotient_sub_derivative (t h : Rat) (hh : h ≠ 0) :
    (pointIm (t + h) - pointIm t) / h - pointImDerivative t =
      (-2 * h * (t * (3 - t * t) + h * (1 - t * t))) /
        ((1 + t * t) * (1 + t * t) * (1 + (t + h) * (t + h))) := by
  rw [pointIm_differenceQuotient t h hh]
  unfold pointImDerivative RationalCircle.Stage.pointDerivative
  dsimp
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  simp only [Rat.inv_mul_rev]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.neg_mul, Rat.mul_neg]

private theorem qabs_factors_le_one {u v : Rat}
    (hu : qabs u <= 1) (hv : qabs v <= 1) :
    qabs u * qabs v <= 1 := by
  calc
    qabs u * qabs v <= 1 * qabs v :=
      Rat.mul_le_mul_of_nonneg_right hu (qabs_nonneg v)
    _ <= 1 * 1 := Rat.mul_le_mul_of_nonneg_left hv (by native_decide)
    _ = 1 := by native_decide

private theorem qabs_step_le_one {t h : Rat}
    (ht0 : 0 <= t) (ht1 : t <= 1)
    (hth0 : 0 <= t + h) (hth1 : t + h <= 1) :
    qabs h <= 1 := by
  apply qabs_le_of_neg_le_le
  · have : 0 <= t + h := hth0
    grind [Rat.sub_eq_add_neg]
  · have : t + h <= 1 := hth1
    grind [Rat.sub_eq_add_neg]

private theorem qabs_unit_le_one {t : Rat} (ht0 : 0 <= t) (ht1 : t <= 1) :
    qabs t <= 1 := by
  rw [qabs_eq_self_of_nonneg ht0]
  exact ht1

private theorem one_le_one_add_square (u : Rat) : 1 <= 1 + u * u := by
  have hsquare : 0 <= u * u := RationalCircle.Stage.ratSquare_nonneg u
  grind

private theorem one_le_mul_of_one_le {a b : Rat}
    (ha : 1 <= a) (hb : 1 <= b) : 1 <= a * b := by
  calc
    1 = 1 * 1 := by native_decide
    _ <= a * 1 := Rat.mul_le_mul_of_nonneg_right ha (by native_decide)
    _ <= a * b := Rat.mul_le_mul_of_nonneg_left hb (by grind)

private theorem one_div_le_one_of_one_le {d : Rat} (hd : 1 <= d) :
    1 / d <= 1 := by
  have hdpos : 0 < d := by grind
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= d := hd
      _ = 1 * d := by grind
  · exact hdpos

private theorem chart_denominator_inv_abs_le_one (t h : Rat) :
    qabs
      (((1 + t * t) * (1 + t * t) *
        (1 + (t + h) * (t + h)))⁻¹) <= 1 := by
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hd : 1 <= d := by
    dsimp [d]
    exact one_le_one_add_square t
  have he : 1 <= e := by
    dsimp [e]
    exact one_le_one_add_square (t + h)
  have hde : 1 <= d * d * e :=
    one_le_mul_of_one_le (one_le_mul_of_one_le hd hd) he
  have hpos : 0 < d * d * e := by grind
  rw [qabs_eq_self_of_nonneg (Rat.le_of_lt ((Rat.inv_pos).2 hpos))]
  have hinv : 1 / (d * d * e) <= 1 := one_div_le_one_of_one_le hde
  simpa [d, e, Rat.div_def] using hinv

private theorem qabs_re_secant_coefficient_le_six {t h : Rat}
    (ht : qabs t <= 1) (hh : qabs h <= 1) :
    qabs (-1 + 3 * t * t + 2 * t * h) <= 6 := by
  have htt : qabs t * qabs t <= 1 := qabs_factors_le_one ht ht
  have hth : qabs t * qabs h <= 1 := qabs_factors_le_one ht hh
  have hthree : qabs (3 : Rat) = 3 := by native_decide
  have htwo : qabs (2 : Rat) = 2 := by native_decide
  have hnegone : qabs (-1 : Rat) = 1 := by native_decide
  have h3tt : qabs (3 * t * t) <= 3 := by
    rw [qabs_mul, qabs_mul, hthree]
    calc
      3 * qabs t * qabs t = 3 * (qabs t * qabs t) := by
        grind [Rat.mul_assoc]
      _ <= 3 * 1 := Rat.mul_le_mul_of_nonneg_left htt (by native_decide)
      _ = 3 := by native_decide
  have h2th : qabs (2 * t * h) <= 2 := by
    rw [qabs_mul, qabs_mul, htwo]
    calc
      2 * qabs t * qabs h = 2 * (qabs t * qabs h) := by
        grind [Rat.mul_assoc]
      _ <= 2 * 1 := Rat.mul_le_mul_of_nonneg_left hth (by native_decide)
      _ = 2 := by native_decide
  calc
    qabs (-1 + 3 * t * t + 2 * t * h) =
        qabs ((-1) + (3 * t * t + 2 * t * h)) := by
          congr 1
          grind [Rat.add_assoc]
    _ <= qabs (-1) + qabs (3 * t * t + 2 * t * h) := qabs_add_le _ _
    _ <= 1 + (qabs (3 * t * t) + qabs (2 * t * h)) := by
      rw [hnegone]
      exact Rat.add_le_add_left (qabs_add_le _ _) _
    _ <= 1 + (3 + 2) := Rat.add_le_add_left
      (Rat.add_le_add h3tt h2th) _
    _ = 6 := by native_decide

private theorem qabs_im_secant_coefficient_le_six {t h : Rat}
    (ht : qabs t <= 1) (hh : qabs h <= 1) :
    qabs (t * (3 - t * t) + h * (1 - t * t)) <= 6 := by
  have htt : qabs t * qabs t <= 1 := qabs_factors_le_one ht ht
  have hth : qabs t * qabs h <= 1 := qabs_factors_le_one ht hh
  have hthree : qabs (3 : Rat) = 3 := by native_decide
  have hone : qabs (1 : Rat) = 1 := by native_decide
  have h3sub : qabs (3 - t * t) <= 4 := by
    calc
      qabs (3 - t * t) <= qabs 3 + qabs (t * t) := qabs_sub_le _ _
      _ = 3 + (qabs t * qabs t) := by rw [qabs_mul, hthree]
      _ <= 3 + 1 := Rat.add_le_add_left htt _
      _ = 4 := by native_decide
  have h1sub : qabs (1 - t * t) <= 2 := by
    calc
      qabs (1 - t * t) <= qabs 1 + qabs (t * t) := qabs_sub_le _ _
      _ = 1 + (qabs t * qabs t) := by rw [qabs_mul, hone]
      _ <= 1 + 1 := Rat.add_le_add_left htt _
      _ = 2 := by native_decide
  have hleft : qabs (t * (3 - t * t)) <= 4 := by
    rw [qabs_mul]
    calc
      qabs t * qabs (3 - t * t) <= 1 * qabs (3 - t * t) :=
        Rat.mul_le_mul_of_nonneg_right ht (qabs_nonneg _)
      _ <= 1 * 4 := Rat.mul_le_mul_of_nonneg_left h3sub (by native_decide)
      _ = 4 := by native_decide
  have hright : qabs (h * (1 - t * t)) <= 2 := by
    rw [qabs_mul]
    calc
      qabs h * qabs (1 - t * t) <= 1 * qabs (1 - t * t) :=
        Rat.mul_le_mul_of_nonneg_right hh (qabs_nonneg _)
      _ <= 1 * 2 := Rat.mul_le_mul_of_nonneg_left h1sub (by native_decide)
      _ = 2 := by native_decide
  calc
    qabs (t * (3 - t * t) + h * (1 - t * t)) <=
        qabs (t * (3 - t * t)) + qabs (h * (1 - t * t)) := qabs_add_le _ _
    _ <= 4 + 2 := Rat.add_le_add hleft hright
    _ = 6 := by native_decide

/-- Uniform finite real-coordinate secant estimate on the unit chart. -/
theorem pointRe_secant_error_le_twelve {t h : Rat}
    (ht0 : 0 <= t) (ht1 : t <= 1)
    (hth0 : 0 <= t + h) (hth1 : t + h <= 1) (hh : h ≠ 0) :
    qabs ((pointRe (t + h) - pointRe t) / h - pointReDerivative t) <=
      12 * qabs h := by
  rw [pointRe_differenceQuotient_sub_derivative t h hh, Rat.div_def, qabs_mul]
  have ht : qabs t <= 1 := qabs_unit_le_one ht0 ht1
  have hstep : qabs h <= 1 := qabs_step_le_one ht0 ht1 hth0 hth1
  have hcoefficient : qabs (-1 + 3 * t * t + 2 * t * h) <= 6 :=
    qabs_re_secant_coefficient_le_six ht hstep
  have htwo : qabs (2 : Rat) = 2 := by native_decide
  have hnumerator :
      qabs (2 * h * (-1 + 3 * t * t + 2 * t * h)) <= 12 * qabs h := by
    rw [qabs_mul, qabs_mul, htwo]
    calc
      2 * qabs h * qabs (-1 + 3 * t * t + 2 * t * h) =
          (2 * qabs h) * qabs (-1 + 3 * t * t + 2 * t * h) := by
            grind [Rat.mul_assoc]
      _ <= (2 * qabs h) * 6 :=
        Rat.mul_le_mul_of_nonneg_left hcoefficient
          (Rat.mul_nonneg (by native_decide) (qabs_nonneg h))
      _ = 12 * qabs h := by grind [Rat.mul_assoc, Rat.mul_comm]
  have hden := chart_denominator_inv_abs_le_one t h
  calc
    qabs (2 * h * (-1 + 3 * t * t + 2 * t * h) ) *
        qabs (((1 + t * t) * (1 + t * t) *
          (1 + (t + h) * (t + h)))⁻¹) <=
        (12 * qabs h) * qabs (((1 + t * t) * (1 + t * t) *
          (1 + (t + h) * (t + h)))⁻¹) :=
      Rat.mul_le_mul_of_nonneg_right hnumerator (qabs_nonneg _)
    _ <= (12 * qabs h) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hden
        (Rat.mul_nonneg (by native_decide) (qabs_nonneg h))
    _ = 12 * qabs h := by rw [Rat.mul_one]

/-- Uniform finite imaginary-coordinate secant estimate on the unit chart. -/
theorem pointIm_secant_error_le_twelve {t h : Rat}
    (ht0 : 0 <= t) (ht1 : t <= 1)
    (hth0 : 0 <= t + h) (hth1 : t + h <= 1) (hh : h ≠ 0) :
    qabs ((pointIm (t + h) - pointIm t) / h - pointImDerivative t) <=
      12 * qabs h := by
  rw [pointIm_differenceQuotient_sub_derivative t h hh, Rat.div_def, qabs_mul]
  have ht : qabs t <= 1 := qabs_unit_le_one ht0 ht1
  have hstep : qabs h <= 1 := qabs_step_le_one ht0 ht1 hth0 hth1
  have hcoefficient : qabs (t * (3 - t * t) + h * (1 - t * t)) <= 6 :=
    qabs_im_secant_coefficient_le_six ht hstep
  have htwo : qabs (-2 : Rat) = 2 := by native_decide
  have hnumerator :
      qabs (-2 * h * (t * (3 - t * t) + h * (1 - t * t))) <= 12 * qabs h := by
    rw [qabs_mul, qabs_mul, htwo]
    calc
      2 * qabs h * qabs (t * (3 - t * t) + h * (1 - t * t)) =
          (2 * qabs h) * qabs (t * (3 - t * t) + h * (1 - t * t)) := by
            grind [Rat.mul_assoc]
      _ <= (2 * qabs h) * 6 :=
        Rat.mul_le_mul_of_nonneg_left hcoefficient
          (Rat.mul_nonneg (by native_decide) (qabs_nonneg h))
      _ = 12 * qabs h := by grind [Rat.mul_assoc, Rat.mul_comm]
  have hden := chart_denominator_inv_abs_le_one t h
  calc
    qabs (-2 * h * (t * (3 - t * t) + h * (1 - t * t))) *
        qabs (((1 + t * t) * (1 + t * t) *
          (1 + (t + h) * (t + h)))⁻¹) <=
        (12 * qabs h) * qabs (((1 + t * t) * (1 + t * t) *
          (1 + (t + h) * (t + h)))⁻¹) :=
      Rat.mul_le_mul_of_nonneg_right hnumerator (qabs_nonneg _)
    _ <= (12 * qabs h) * 1 :=
      Rat.mul_le_mul_of_nonneg_left hden
        (Rat.mul_nonneg (by native_decide) (qabs_nonneg h))
    _ = 12 * qabs h := by rw [Rat.mul_one]

/-- The chart's angular coefficient is exactly the already-certified sector
area speed.  Thus the reparametrization required for a constant rotation
generator is the same geometric arctangent-area parameter used for pi. -/
theorem angularVelocity_eq_imaginaryAxis_sectorAreaSpeed (t : Rat) :
    angularVelocity t =
      RotationSeries.imaginaryAxis (RationalCircle.Stage.sectorAreaSpeed t) := by
  unfold angularVelocity
  rw [RationalCircle.Stage.sectorAreaSpeed_eq_two_over_one_plus_square,
    RotationSeries.imaginaryAxis_coordinates]

/-- Exact rational form of the chart's rotation equation.  This is the
algebraic kernel needed to compare the rational-circle quarter turn with the
constant-generator Peano--Baker rotation after reparametrization by the
sector-area angle. -/
theorem pointComplexDerivative_eq_angularVelocity_mul_point (t : Rat) :
    pointComplexDerivative t = QComplex.mul (angularVelocity t) (pointComplex t) := by
  unfold pointComplexDerivative angularVelocity pointComplex
    RationalCircle.Stage.pointDerivative RationalCircle.Stage.point QComplex.mul
  dsimp
  apply RotationSeries.qcomplex_ext
  · change (-4 * t) / ((1 + t * t) * (1 + t * t)) =
      0 * ((1 - t * t) / (1 + t * t)) -
        (2 / (1 + t * t)) * (2 * t / (1 + t * t))
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
    simp only [Rat.zero_mul, Rat.sub_eq_add_neg]
    rw [Rat.inv_mul_rev]
    grind [Rat.neg_mul, Rat.mul_neg, Rat.mul_assoc, Rat.mul_comm]
  · change (2 * (1 - t * t)) / ((1 + t * t) * (1 + t * t)) =
      0 * (2 * t / (1 + t * t)) +
        (2 / (1 + t * t)) * ((1 - t * t) / (1 + t * t))
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
    simp only [Rat.zero_mul, Rat.zero_add]
    rw [Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm]

/-- The same velocity identity stated directly with the geometric sector-area
speed.  It is the precise finite hand-off from the rational circle to a
Peano--Baker rotation in sector-area time. -/
theorem pointComplexDerivative_eq_sectorAreaSpeed_rotation (t : Rat) :
    pointComplexDerivative t =
      QComplex.mul
        (RotationSeries.imaginaryAxis (RationalCircle.Stage.sectorAreaSpeed t))
        (pointComplex t) := by
  rw [← angularVelocity_eq_imaginaryAxis_sectorAreaSpeed]
  exact pointComplexDerivative_eq_angularVelocity_mul_point t

end GeometricRotationODE

end ComputableAnalysis
