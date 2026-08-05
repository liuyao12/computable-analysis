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

theorem pointComplex_zero : pointComplex 0 = QComplex.one := by
  native_decide

theorem pointComplex_one : pointComplex 1 = RotationSeries.imaginaryUnit := by
  native_decide

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
