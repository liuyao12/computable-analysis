import ComputableAnalysis.ArctanGeometry
import ComputableAnalysis.RotationLift

/-!
# A represented geometric half-pi rotation

This is the direct geometric input path for the factorial rotation evaluator.
It deliberately depends only on the geometric arctangent computation, not on
the larger pi-presentation registry.  The raw half angle is sampled on a
cofinal rational schedule so that its explicit width bound has exactly the
modulus required by `RotationLift`.
-/

namespace ComputableAnalysis

namespace GeometricPiRotation

/-- The literal geometric half angle: `2 * arctan.geom(1)`. -/
def halfPiUnscheduled : RealRaw :=
  (2 : Nat) * ArctanGeometry.arctanGeom (1 : Rat)

theorem halfPiUnscheduled_valid : halfPiUnscheduled.Valid := by
  unfold halfPiUnscheduled
  exact RealRaw.natScale_valid 2
    (ArctanGeometry.arctanGeom_valid_on_unit
      (by native_decide) (by native_decide))

/-- A cofinal rational schedule that turns the elementary geometric width
bound into the input modulus used by the represented-angle rotation lift. -/
def halfPiStageSchedule : RealRaw.StageSchedule where
  stage := fun n => 4 * n + 3
  monotone := by
    intro i j hij
    omega
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    omega

/-- The certified geometric representative of `pi / 2`.  It is the same
geometric calculation as `2 * arctan.geom(1)`, merely observed at a faster
cofinal sequence of finite stages. -/
def halfPi : RealRaw :=
  RealRaw.schedule halfPiStageSchedule halfPiUnscheduled

theorem halfPi_valid : halfPi.Valid := by
  unfold halfPi
  exact RealRaw.schedule_valid halfPiUnscheduled halfPiUnscheduled_valid
    halfPiStageSchedule

theorem halfPi_equiv_unscheduled : halfPi.Equiv halfPiUnscheduled := by
  exact RealRaw.equiv_symm
    (RealRaw.schedule_equiv halfPiUnscheduled halfPiUnscheduled_valid
      halfPiStageSchedule)

/-- The normalized geometric quarter-turn raw is valid because its rational
boxes are literally the doubled unit-slope geometric arctangent boxes. -/
theorem geometricQuarterTurnOne_valid :
    (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)).Valid := by
  change RealRaw.ValidCompute
    ((RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)).compute)
  rw [← funext (fun n =>
    ArctanGeometry.two_arctanGeom_one_compute_eq_quarterTurnRaw_one_compute n)]
  simpa [halfPiUnscheduled] using halfPiUnscheduled_valid

/-- The cofinally scheduled geometric half angle is equivalent to the
normalized rational-circle quarter turn. -/
theorem halfPi_equiv_geometricQuarterTurnOne :
    halfPi.Equiv (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)) := by
  have hdirect : halfPiUnscheduled.Equiv
      (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)) := by
    simpa [halfPiUnscheduled] using
      ArctanGeometry.two_arctanGeom_one_equiv_quarterTurnRaw_one
  exact RealRaw.equiv_trans halfPi_valid halfPiUnscheduled_valid
    geometricQuarterTurnOne_valid halfPi_equiv_unscheduled hdirect

/-- The unscheduled geometric half angle starts in the elementary enclosure
`[1,2]`; every later box is nested inside it. -/
theorem halfPiUnscheduled_compute_zero :
    halfPiUnscheduled.compute 0 = { lo := 1, hi := 2 } := by
  native_decide

/-- Every scheduled geometric half-angle box remains in `[1,2]`. -/
theorem halfPi_bounds (n : Nat) :
    (1 : Rat) <= (halfPi.compute n).lo /\
      (halfPi.compute n).hi <= 2 := by
  have hnest := halfPiUnscheduled_valid.2.1 0
    (halfPiStageSchedule.stage n) (Nat.zero_le _)
  rw [halfPiUnscheduled_compute_zero] at hnest
  simpa [halfPi, RealRaw.schedule] using ⟨hnest.1, hnest.2.2⟩

/-- Before rescheduling, the doubled geometric sector computation has the
explicit elementary width bound `8 / (m + 1)`. -/
theorem halfPiUnscheduled_width_le_eight_div_succ (m : Nat) :
    (halfPiUnscheduled.compute m).width <=
      8 / (((m + 1 : Nat) : Rat)) := by
  have hgeom := ArctanGeometry.positiveLoopComputeAtStage_width_le_four_div_succ
    (x := (1 : Rat)) (by native_decide) (by native_decide) m
  have htwo : (0 : Rat) <= 2 := by native_decide
  unfold halfPiUnscheduled
  change ((RealRaw.scaleRat 2 (ArctanGeometry.arctanGeom 1)).compute m).width <=
    8 / (((m + 1 : Nat) : Rat))
  rw [RealRaw.scaleRat_width_of_nonneg htwo,
    ArctanGeometry.arctanGeom_one_compute_eq]
  calc
    2 * (ArctanGeometry.positiveLoopComputeAtStage 1 m).width <=
        2 * (4 / (((m + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hgeom htwo
    _ = 8 / (((m + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The cofinal schedule provides the `2 / (n + 1)` modulus needed by the
generic represented-angle rotation algorithm. -/
theorem halfPi_width_le_two_div_succ (n : Nat) :
    (halfPi.compute n).width <= 2 / (((n + 1 : Nat) : Rat)) := by
  change (halfPiUnscheduled.compute (4 * n + 3)).width <=
    2 / (((n + 1 : Nat) : Rat))
  calc
    (halfPiUnscheduled.compute (4 * n + 3)).width <=
        8 / ((((4 * n + 3) + 1 : Nat) : Rat)) :=
      halfPiUnscheduled_width_le_eight_div_succ (4 * n + 3)
    _ = 2 / (((n + 1 : Nat) : Rat)) := by
      have hstage : 4 * n + 3 + 1 = 4 * (n + 1) := by omega
      rw [hstage]
      push_cast
      rw [Rat.div_def, Rat.div_def]
      have hfour : (4 : Rat) * (4 : Rat)⁻¹ = 1 := by
        exact Rat.mul_inv_cancel 4 (by native_decide)
      rw [Rat.inv_mul_rev]
      calc
        8 * (((n : Rat) + 1)⁻¹ * (4 : Rat)⁻¹) =
            (2 * ((4 : Rat) * (4 : Rat)⁻¹)) * ((n : Rat) + 1)⁻¹ := by
          grind [Rat.mul_assoc, Rat.mul_comm]
        _ = 2 * ((n : Rat) + 1)⁻¹ := by rw [hfour, Rat.mul_one]

/-- The finite certificate consumed by the generic rotation lift. -/
def halfPiInput : RotationLift.HalfPiInput where
  raw := halfPi
  valid := halfPi_valid
  bounds := halfPi_bounds
  width_le_two_div_succ := halfPi_width_le_two_div_succ

/-- The direct rational midpoint factorial candidates for the geometric
half-angle. -/
def rotationCandidate : ComplexRaw :=
  RotationLift.HalfPiInput.rotationCandidate halfPiInput

theorem rotationCandidate_compute (n : Nat) :
    rotationCandidate.compute n =
      RotationSeries.uniformRotationBox (halfPi.compute n).midpoint n := by
  simpa [rotationCandidate, halfPiInput] using
    RotationLift.HalfPiInput.rotationCandidate_compute halfPiInput n

theorem rotationCandidate_ordered (n : Nat) :
    (rotationCandidate.compute n).Ordered := by
  simpa [rotationCandidate] using
    RotationLift.HalfPiInput.rotationCandidate_ordered halfPiInput n

theorem rotationCandidate_widths_shrink :
    ComplexRaw.WidthsShrinkToZero rotationCandidate.compute := by
  simpa [rotationCandidate] using
    RotationLift.HalfPiInput.rotationCandidate_widths_shrink halfPiInput

/-- The exact rational radius added to control movement between half-angle
midpoints. -/
def rotationRadius (n : Nat) : Rat :=
  RotationLift.HalfPiInput.rotationRadius halfPiInput n

theorem rotationRadius_shrinks : ShrinksToZero rotationRadius := by
  simpa [rotationRadius] using
    RotationLift.HalfPiInput.rotationRadius_shrinks halfPiInput

/-- A valid represented complex rotation at the geometric angle `pi / 2`.
Its construction is finite prefix stabilization of rational factorial boxes. -/
def rotation : ComplexRaw :=
  RotationLift.HalfPiInput.rotation halfPiInput

theorem rotation_valid : rotation.Valid := by
  simpa [rotation] using
    RotationLift.HalfPiInput.rotation_valid halfPiInput

theorem rotation_contains_current_candidate (n : Nat) :
    QBox.NestedIn (rotationCandidate.compute n) (rotation.compute n) := by
  simpa [rotationCandidate, rotation] using
    RotationLift.HalfPiInput.rotation_contains_current_candidate halfPiInput n

/-- The corresponding valid represented imaginary input `i * pi / 2`. -/
def imaginaryHalf : ComplexRaw :=
  ComplexRaw.imaginaryAxis halfPi

theorem imaginaryHalf_valid : imaginaryHalf.Valid := by
  unfold imaginaryHalf
  exact ComplexRaw.imaginaryAxis_valid halfPi_valid

end GeometricPiRotation

end ComputableAnalysis
