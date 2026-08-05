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

/-- The real coordinate of the rational circle chart, exposed separately for
finite-difference certificates. -/
def pointRe (t : Rat) : Rat := (RationalCircle.Stage.point t).x

/-- The imaginary coordinate of the rational circle chart, exposed separately
for finite-difference certificates. -/
def pointIm (t : Rat) : Rat := (RationalCircle.Stage.point t).y

/-- The exact rational velocity in the real coordinate. -/
def pointReDerivative (t : Rat) : Rat :=
  (RationalCircle.Stage.pointDerivative t).x

/-- The exact rational velocity in the imaginary coordinate. -/
def pointImDerivative (t : Rat) : Rat :=
  (RationalCircle.Stage.pointDerivative t).y

private theorem rat_eq_of_right_mul_eq_mul_ne {a b c : Rat}
    (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hc
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem pointComplex_zero : pointComplex 0 = QComplex.one := by
  native_decide

theorem pointComplex_one : pointComplex 1 = RotationSeries.imaginaryUnit := by
  native_decide

/-- Exact finite quotient for the chart's real coordinate.  This is the first
portable algebraic ingredient of the represented derivative certificate. -/
theorem pointRe_differenceQuotient (t h : Rat) (hh : h ≠ 0) :
    (pointRe (t + h) - pointRe t) / h =
      (-2 * (2 * t + h)) /
        ((1 + t * t) * (1 + (t + h) * (t + h))) := by
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos t
  have hepos : 0 < e := by
    dsimp [e]
    exact RationalCircle.Stage.one_add_square_pos (t + h)
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hene : e ≠ 0 := Rat.ne_of_gt hepos
  have hprod : h * d * e ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hh hzero
      · exact hdne hzero
    · exact hene hzero
  apply rat_eq_of_right_mul_eq_mul_ne hprod
  unfold pointRe RationalCircle.Stage.point
  change (((1 - (t + h) * (t + h)) / e - (1 - t * t) / d) / h) *
      (h * d * e) = ((-2 * (2 * t + h)) / (d * e)) * (h * d * e)
  rw [Rat.div_def]
  have hcancelH : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
  have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
  have hcancelE : e⁻¹ * e = 1 := Rat.inv_mul_cancel e hene
  have hcancelDE : (d * e)⁻¹ * (d * e) = 1 :=
    Rat.inv_mul_cancel (d * e) (by
      intro hzero
      rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hene hzero)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Exact finite quotient for the chart's imaginary coordinate. -/
theorem pointIm_differenceQuotient (t h : Rat) (hh : h ≠ 0) :
    (pointIm (t + h) - pointIm t) / h =
      (2 * (1 - t * t - t * h)) /
        ((1 + t * t) * (1 + (t + h) * (t + h))) := by
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos t
  have hepos : 0 < e := by
    dsimp [e]
    exact RationalCircle.Stage.one_add_square_pos (t + h)
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hene : e ≠ 0 := Rat.ne_of_gt hepos
  have hprod : h * d * e ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hh hzero
      · exact hdne hzero
    · exact hene hzero
  apply rat_eq_of_right_mul_eq_mul_ne hprod
  unfold pointIm RationalCircle.Stage.point
  change (((2 * (t + h)) / e - (2 * t) / d) / h) * (h * d * e) =
      ((2 * (1 - t * t - t * h)) / (d * e)) * (h * d * e)
  rw [Rat.div_def]
  have hcancelH : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
  have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
  have hcancelE : e⁻¹ * e = 1 := Rat.inv_mul_cancel e hene
  have hcancelDE : (d * e)⁻¹ * (d * e) = 1 :=
    Rat.inv_mul_cancel (d * e) (by
      intro hzero
      rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hene hzero)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Exact real-coordinate secant error relative to the named rational
velocity.  Its explicit factor of `h` is the starting point for a quantitative
derivative modulus. -/
theorem pointRe_differenceQuotient_sub_derivative (t h : Rat) (hh : h ≠ 0) :
    (pointRe (t + h) - pointRe t) / h - pointReDerivative t =
      (2 * h * (-1 + 3 * t * t + 2 * t * h)) /
        ((1 + t * t) * (1 + t * t) * (1 + (t + h) * (t + h))) := by
  rw [pointRe_differenceQuotient t h hh]
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos t
  have hepos : 0 < e := by
    dsimp [e]
    exact RationalCircle.Stage.one_add_square_pos (t + h)
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hene : e ≠ 0 := Rat.ne_of_gt hepos
  have hprod : d * d * e ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hdne hzero
    · exact hene hzero
  apply rat_eq_of_right_mul_eq_mul_ne hprod
  unfold pointReDerivative RationalCircle.Stage.pointDerivative
  dsimp
  change (((-2 * (2 * t + h)) / (d * e) - (-4 * t) / (d * d))) *
      (d * d * e) =
    ((2 * h * (-1 + 3 * t * t + 2 * t * h)) / (d * d * e)) *
      (d * d * e)
  rw [Rat.div_def]
  simp only [Rat.inv_mul_rev]
  have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
  have hcancelE : e⁻¹ * e = 1 := Rat.inv_mul_cancel e hene
  have hcancelDD : (d * d)⁻¹ * (d * d) = 1 :=
    Rat.inv_mul_cancel (d * d) (by
      intro hzero
      rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hdne hzero)
  have hcancelDDE : (d * d * e)⁻¹ * (d * d * e) = 1 :=
    Rat.inv_mul_cancel (d * d * e) hprod
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.neg_mul, Rat.mul_neg]

/-- Exact imaginary-coordinate secant error relative to the named rational
velocity. -/
theorem pointIm_differenceQuotient_sub_derivative (t h : Rat) (hh : h ≠ 0) :
    (pointIm (t + h) - pointIm t) / h - pointImDerivative t =
      (-2 * h * (t * (3 - t * t) + h * (1 - t * t))) /
        ((1 + t * t) * (1 + t * t) * (1 + (t + h) * (t + h))) := by
  rw [pointIm_differenceQuotient t h hh]
  let d := 1 + t * t
  let e := 1 + (t + h) * (t + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos t
  have hepos : 0 < e := by
    dsimp [e]
    exact RationalCircle.Stage.one_add_square_pos (t + h)
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hene : e ≠ 0 := Rat.ne_of_gt hepos
  have hprod : d * d * e ≠ 0 := by
    intro hzero
    rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
    · rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hdne hzero
    · exact hene hzero
  apply rat_eq_of_right_mul_eq_mul_ne hprod
  unfold pointImDerivative RationalCircle.Stage.pointDerivative
  dsimp
  change (((2 * (1 - t * t - t * h)) / (d * e) -
      (2 * (1 - t * t)) / (d * d))) * (d * d * e) =
    ((-2 * h * (t * (3 - t * t) + h * (1 - t * t))) /
      (d * d * e)) * (d * d * e)
  rw [Rat.div_def]
  simp only [Rat.inv_mul_rev]
  have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
  have hcancelE : e⁻¹ * e = 1 := Rat.inv_mul_cancel e hene
  have hcancelDD : (d * d)⁻¹ * (d * d) = 1 :=
    Rat.inv_mul_cancel (d * d) (by
      intro hzero
      rcases Rat.mul_eq_zero.mp hzero with hzero | hzero
      · exact hdne hzero
      · exact hdne hzero)
  have hcancelDDE : (d * d * e)⁻¹ * (d * d * e) = 1 :=
    Rat.inv_mul_cancel (d * d * e) hprod
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.neg_mul, Rat.mul_neg]

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
