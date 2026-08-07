import ComputableAnalysis.GeometricRotationODE
import ComputableAnalysis.IntegralIdentities

/-!
# Sector-area time for the rational circle chart

The rational-circle chart has variable angular speed
`2 / (1 + t^2)`.  This module packages its primitive as an interval-domain
function and gives the explicit epsilon--delta derivative certificate needed
to reparametrize by sector-area time.  It intentionally stops before the
inverse/reparametrized-curve and vector-uniqueness arguments.
-/

namespace ComputableAnalysis

namespace SectorAreaReparametrization

/-- Twice the rectangle arctangent on the rational unit chart.  At `t = 1`
this is the sector angle `pi / 2`; pointwise it is the angle coordinate whose
derivative is the rational-circle angular speed. -/
def angleOnUnit : FunctionOnInterval :=
  FunctionOnInterval.scaleRat 2
    IntegralIdentities.arctanIntegralRectangleOnUnit

/-- The exact rational angular-speed function on the same chart. -/
def speedOnUnit : FunctionOnInterval :=
  FunctionOnInterval.scaleRat 2
    IntegralIdentities.arctanKernelIntervalAtOne

private theorem unit_square_le_one {x : Rat}
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    x * x <= 1 := by
  calc
    x * x <= x * 1 := Rat.mul_le_mul_of_nonneg_left hx1 hx0
    _ = x := by grind
    _ <= 1 := hx1

private theorem one_div_antitone_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : a ≠ 0 := Rat.ne_of_gt ha
  have hbne : b ≠ 0 := Rat.ne_of_gt hb
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · calc
      (1 / b) * (a * b) = a := by
        rw [Rat.div_def]
        have hcancel : b * b⁻¹ = 1 := Rat.mul_inv_cancel b hbne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= b := hab
      _ = (1 / a) * (a * b) := by
        rw [Rat.div_def]
        have hcancel : a * a⁻¹ = 1 := Rat.mul_inv_cancel a hane
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact habpos

/-- On the unit chart the sector-speed kernel is at least one half.  This is
the finite lower-growth fact that turns weak monotonicity into an effective
inverse-separation certificate. -/
private theorem integralKernel_one_half_le {x : Rat}
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    (1 : Rat) / 2 <= ArctanGeometry.integralKernel x := by
  let d : Rat := 1 + x * x
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos x
  have hdle : d <= 2 := by
    dsimp [d]
    have hsq := unit_square_le_one hx0 hx1
    grind
  unfold ArctanGeometry.integralKernel
  exact one_div_antitone_of_pos_of_le hdpos hdle

/-- A stage `64 (n+1)` makes each unscaled rectangle-arctangent box no wider
than one sixteenth of the requested input separation `1/(n+1)`. -/
private theorem rectangle_width_le_sixteenth_input_precision
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width <=
      1 / (16 * ((n + 1 : Nat) : Rat)) := by
  have hbound := ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
    hx0 hx1 (64 * (n + 1))
  let d : Rat := ((n + 1 : Nat) : Rat)
  let e : Rat := ((64 * (n + 1) + 1 : Nat) : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have heq : e = 64 * d + 1 := by
    dsimp [e, d]
    rw [Rat.natCast_add, Rat.natCast_mul]
    change (64 : Rat) * ((n + 1 : Nat) : Rat) + 1 =
      64 * ((n + 1 : Nat) : Rat) + 1
    rfl
  have hepos : 0 < e := by
    rw [heq]
    have : 0 <= 64 * d := Rat.mul_nonneg (by native_decide) (Rat.le_of_lt hdpos)
    grind
  have hscaledpos : 0 < e * (16 * d) :=
    Rat.mul_pos hepos (Rat.mul_pos (by native_decide) hdpos)
  change (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width <=
    4 / e at hbound
  calc
    (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width <=
        4 / e := hbound
    _ <= 1 / (16 * d) := by
      apply Rat.le_of_mul_le_mul_right (c := e * (16 * d))
      · calc
          (4 / e) * (e * (16 * d)) = 64 * d := by
            rw [Rat.div_def]
            have hcancel : e⁻¹ * e = 1 := Rat.inv_mul_cancel e
              (Rat.ne_of_gt hepos)
            grind [Rat.mul_assoc, Rat.mul_comm]
          _ <= 64 * d + 1 := by grind
          _ = (1 / (16 * d)) * (e * (16 * d)) := by
            rw [Rat.div_def]
            have hcancel : (16 * d)⁻¹ * (16 * d) = 1 := Rat.inv_mul_cancel _
              (Rat.ne_of_gt (Rat.mul_pos (by native_decide) hdpos))
            rw [← heq]
            grind [Rat.mul_assoc, Rat.mul_comm]
      · exact hscaledpos

/-- A rational input separation of `1/(n+1)` strictly separates the finite
rectangle-arctangent boxes at the explicit finer stage `64 (n+1)`.  The proof
is an entirely finite lower-tail comparison: the appended cell from `x` to
`y` has area at least half its rational width, while both endpoint boxes use
less than one eighth of that width together. -/
private theorem arctan_rectangle_boxes_strictly_separated
    {x y : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1) (n : Nat)
    (hsep : x + 1 / (((n + 1 : Nat) : Rat)) <= y) :
    (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).hi <
      (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).lo := by
  let d : Rat := ((n + 1 : Nat) : Rat)
  let delta : Rat := 1 / d
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 hdpos
  have hsep' : x + delta <= y := by
    simpa [delta, d] using hsep
  have hxy : x <= y := by
    have : 0 <= delta := Rat.le_of_lt hdeltaPos
    grind
  let left : List (Rat × Rat) :=
    (ArctanGeometry.arctanAreaLoopState x (64 * (n + 1))).intervals
  let right : List (Rat × Rat) :=
    (ArctanGeometry.arctanAreaLoopState y (64 * (n + 1))).intervals
  have hleft : ArctanGeometry.CoversInterval 0 x left := by
    dsimp [left]
    exact ArctanGeometry.arctanAreaLoopState_intervals_covers hx0 _
  have hright : ArctanGeometry.CoversInterval 0 y right := by
    dsimp [right]
    exact ArctanGeometry.arctanAreaLoopState_intervals_covers hy0 _
  have hcover : ArctanGeometry.CoversInterval 0 y (left ++ [(x, y)]) :=
    ArctanGeometry.CoversInterval.extend_right hleft hxy
  have hcompare :
      ArctanGeometry.integralLowerSum (left ++ [(x, y)]) <=
        ArctanGeometry.integralUpperSum right :=
    ArctanGeometry.integralLowerSum_le_integralUpperSum_of_covers
      (a := 0) (b := y) (by native_decide) (left ++ [(x, y)]) right
      hcover hright
  rw [ArctanGeometry.integralLowerSum_append] at hcompare
  have hcompareTail :
      ArctanGeometry.integralLowerSum left +
        ArctanGeometry.integralLowerStep x y <=
      ArctanGeometry.integralUpperSum right := by
    simpa [ArctanGeometry.integralLowerSum, Rat.add_zero] using hcompare
  have hcompare' :
      (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
        (y - x) * ArctanGeometry.integralKernel y <=
      (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).hi := by
    simpa [left, right, ArctanGeometry.arctanIntegralRectangleCompute,
      ArctanGeometry.integralLowerStep] using hcompareTail
  have hstep : delta <= y - x := by
    grind [Rat.sub_eq_add_neg]
  have htail : delta / 2 <= (y - x) * ArctanGeometry.integralKernel y := by
    have hkernel := integralKernel_one_half_le hy0 hy1
    calc
      delta / 2 = delta * ((1 : Rat) / 2) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
      _ <= (y - x) * ((1 : Rat) / 2) :=
        Rat.mul_le_mul_of_nonneg_right hstep (by native_decide)
      _ <= (y - x) * ArctanGeometry.integralKernel y :=
        Rat.mul_le_mul_of_nonneg_left hkernel (by grind [Rat.sub_eq_add_neg])
  have hwidthX := rectangle_width_le_sixteenth_input_precision hx0 hx1 n
  have hwidthY := rectangle_width_le_sixteenth_input_precision hy0 hy1 n
  have hsixteenth : 1 / (16 * d) = delta / 16 := by
    dsimp [delta]
    rw [Rat.div_def, Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hwidthX' :
      (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width <=
        delta / 16 := by
    rw [← hsixteenth]
    simpa [d] using hwidthX
  have hwidthY' :
      (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).width <=
        delta / 16 := by
    rw [← hsixteenth]
    simpa [d] using hwidthY
  have herrors :
      (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width +
        (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).width <=
          delta / 8 := by
    calc
      (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width +
          (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).width <=
            delta / 16 + delta / 16 := by
              exact rat_add_le_add hwidthX' hwidthY'
      _ = delta / 8 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hmargin :
      (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width +
        (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).width <
          (y - x) * ArctanGeometry.integralKernel y := by
    have hsmall : delta / 8 < delta / 2 := by
      calc
        delta / 8 = delta * ((1 : Rat) / 8) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc]
        _ < delta * ((1 : Rat) / 2) := by
          have hfactor : (1 : Rat) / 8 < 1 / 2 := by native_decide
          exact Rat.mul_lt_mul_of_pos_left hfactor hdeltaPos
        _ = delta / 2 := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc]
    grind
  have hupperX :
      (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).hi <=
        (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
          (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width := by
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hsum :
      (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).hi +
        (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).width <
          (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).hi := by
    have hfirst :
        (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).hi +
            (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).width <=
          (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
            (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width +
            (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).width :=
      (Rat.add_le_add_right).2 hupperX
    have hsecond :
        (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
            (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).width +
            (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).width <
          (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
            (y - x) * ArctanGeometry.integralKernel y := by
      grind [Rat.sub_eq_add_neg]
    grind [Rat.sub_eq_add_neg]
  unfold QInterval.width at hsum
  grind [Rat.sub_eq_add_neg]
  

/-- Scaling the rectangle-sector coordinate by the positive rational `2`
preserves its finite nondecreasing order certificate. -/
theorem angleOnUnit_nondecreasing : NondecreasingOnInterval angleOnUnit := by
  intro x y hx hy hxy n
  have hbase := IntegralIdentities.arctanIntegralRectangleOnUnit_nondecreasing
    x y hx hy hxy n
  change
    (QInterval.scaleRat 2
      (IntegralIdentities.arctanIntegralRectangleOnUnit.compute x hx n)).lo <=
      (QInterval.scaleRat 2
        (IntegralIdentities.arctanIntegralRectangleOnUnit.compute y hy n)).hi
  change 2 *
      (IntegralIdentities.arctanIntegralRectangleOnUnit.compute x hx n).lo <=
    2 *
      (IntegralIdentities.arctanIntegralRectangleOnUnit.compute y hy n).hi
  exact Rat.mul_le_mul_of_nonneg_left hbase (by native_decide)

/-- The weak monotonicity package for the sector-area clock. -/
def angleOnUnit_monotone : MonotoneOnInterval angleOnUnit :=
  MonotoneOnInterval.ofNondecreasing angleOnUnit_nondecreasing

/-- A visible rational gap in chart parameter produces a strict finite gap in
the doubled sector-area boxes.  This is the positive-scaling form of the
rectangle tail estimate above. -/
theorem angleOnUnit_boxes_strictly_separated
    {x y : Rat}
    (hx : inDomainInterval angleOnUnit.lower angleOnUnit.upper x)
    (hy : inDomainInterval angleOnUnit.lower angleOnUnit.upper y)
    (n : Nat)
    (hsep : x + 1 / (((n + 1 : Nat) : Rat)) <= y) :
    (angleOnUnit.compute x hx (64 * (n + 1))).hi <
      (angleOnUnit.compute y hy (64 * (n + 1))).lo := by
  have hbase := arctan_rectangle_boxes_strictly_separated
    hx.1 hx.2 hy.1 hy.2 n hsep
  change 2 *
      (ArctanGeometry.arctanIntegralRectangleCompute x (64 * (n + 1))).hi <
    2 *
      (ArctanGeometry.arctanIntegralRectangleCompute y (64 * (n + 1))).lo
  exact Rat.mul_lt_mul_of_pos_left hbase (by native_decide)

/-- The sector-area clock has the quantitative strict-order data required by
the project's constructive inverse-function interface.  Its input gap is
`1/(n+1)` and a finite rectangle stage `64(n+1)` exposes that gap. -/
def angleOnUnit_effectiveInverseSeparation :
    EffectiveInverseSeparation angleOnUnit where
  kind := .nondecreasing
  inputPrecision := fun n => n + 1
  inputPrecision_pos := fun n => Nat.succ_pos n
  outputPrecision := fun n => 64 * (n + 1)
  separated := by
    intro x y hx hy n hsep
    exact angleOnUnit_boxes_strictly_separated hx hy n hsep

/-- The sector-area angle has derivative equal to the sector-area speed.
The proof is the generic finite scaling rule applied to the checked rectangle
arctangent derivative: no inverse function or ODE iteration is used here. -/
def angleOnUnit_hasDerivative :
    HasDerivativeOnInterval angleOnUnit speedOnUnit := by
  exact IntegralIdentities.arctanIntegralRectangleOnUnit_hasDerivative.scaleRat_two

/-- Evaluate the represented sector-area angle at a rational point of its
unit chart. -/
def angleAt (t : Rat) (ht : inDomainInterval angleOnUnit.lower angleOnUnit.upper t) :
    RealRaw :=
  PartialRealFunRaw.apply angleOnUnit.raw angleOnUnit.valid_on t
    (angleOnUnit.defined_on t ht)

theorem angleAt_valid
    (t : Rat) (ht : inDomainInterval angleOnUnit.lower angleOnUnit.upper t) :
    (angleAt t ht).Valid :=
  angleOnUnit.valid_on t (angleOnUnit.defined_on t ht)

/-- The rectangle-sector angle is pointwise equivalent to twice the geometric
arctangent.  This remains a raw-real equivalence on rational inputs; no
completion or extension to an irrational domain is used. -/
theorem angleAt_equiv_two_arctanGeom
    (t : Rat) (ht : inDomainInterval angleOnUnit.lower angleOnUnit.upper t) :
    (angleAt t ht).Equiv ((2 : Nat) * ArctanGeometry.arctanGeom t) := by
  have ht' : 0 <= t /\ t <= 1 := by
    simpa [angleOnUnit, FunctionOnInterval.scaleRat, inDomainInterval] using ht
  have hrect := IntegralIdentities.arctanIntegralRectangleFor_equiv_arctanGeom
    t ht'.1 ht'.2
  have hscaled := RealRaw.scaleRat_equiv_of_nonneg (r := (2 : Rat))
    (by native_decide) hrect
  change (RealRaw.scaleRat 2
      (IntegralIdentities.arctanIntegralRectangleFor t ht'.1 ht'.2)).Equiv _
  simpa using hscaled

/-- At each rational input, the scaled exact kernel evaluator is literally
the rational-circle sector-area speed. -/
theorem speedOnUnit_compute_eq_sectorAreaSpeed
    (t : Rat) (ht : inDomainInterval speedOnUnit.lower speedOnUnit.upper t)
    (n : Nat) :
    speedOnUnit.compute t ht n =
      { lo := RationalCircle.Stage.sectorAreaSpeed t,
        hi := RationalCircle.Stage.sectorAreaSpeed t } := by
  change (FunctionOnInterval.scaleRat 2
      IntegralIdentities.arctanKernelIntervalAtOne).compute t ht n = _
  rw [FunctionOnInterval.scaleRat_compute]
  change QInterval.scaleRat 2
      { lo := 1 / (1 + t * t), hi := 1 / (1 + t * t) } = _
  rw [RationalCircle.Stage.sectorAreaSpeed_eq_two_over_one_plus_square]
  simp [QInterval.scaleRat, Rat.div_def]

/-- The speed component of the reparametrization is the exact coefficient in
the geometric chart's variable-coefficient rotation equation. -/
theorem speedOnUnit_value_eq_geometricAngularSpeed
    (t : Rat) (ht : inDomainInterval speedOnUnit.lower speedOnUnit.upper t)
    (n : Nat) :
    RotationSeries.imaginaryAxis
      (speedOnUnit.compute t ht n).lo =
      GeometricRotationODE.angularVelocity t := by
  rw [speedOnUnit_compute_eq_sectorAreaSpeed t ht n]
  rw [GeometricRotationODE.angularVelocity_eq_imaginaryAxis_sectorAreaSpeed]

end SectorAreaReparametrization

end ComputableAnalysis
