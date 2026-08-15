import ComputableAnalysis.GeometricPiRotation
import ComputableAnalysis.SectorAreaReparametrization

/-!
# Lifting the sector-area endpoint through the factorial rotation

The accelerated rectangle-sector clock already computes the geometric
quarter-turn angle at the rational endpoint `t = 1`.  This file packages that
specific raw endpoint as an input for the bounded factorial rotation lift and
transports the resulting complex raw to the geometry-only rotation
presentation.  It stops before the separate ODE uniqueness argument that
would identify this factorial rotation with the rational-circle point `i`.
-/

namespace ComputableAnalysis

namespace SectorAreaRotation

/-- The elementary proof that the rational circle-chart endpoint lies on the
unit interval.  Naming it makes the endpoint raw and its accompanying finite
bounds reusable without exposing a proof-term-dependent interface. -/
def unitEndpoint :
    inDomainInterval
      SectorAreaReparametrization.angleOnUnitRegular.lower
      SectorAreaReparametrization.angleOnUnitRegular.upper (1 : Rat) := by
  change (0 : Rat) <= 1 /\ 1 <= (1 : Rat)
  native_decide

/-- The accelerated sector-area angle at the unit chart endpoint. -/
def halfPi : RealRaw :=
  SectorAreaReparametrization.regularAngleAt (1 : Rat) unitEndpoint

theorem halfPi_valid : halfPi.Valid :=
  SectorAreaReparametrization.regularAngleAt_valid (1 : Rat) unitEndpoint

/-- Every accelerated rectangle endpoint box is inside the uniform factorial
input chart `[1,2]`.  The lower estimate is bounded by the endpoint kernel
`1/(1+1^2)=1/2`, while the upper estimate is bounded by the interval length;
thus this is a uniform rational inequality, not a decimal approximation. -/
theorem halfPi_bounds (n : Nat) :
    (1 : Rat) <= (halfPi.compute n).lo /\
      (halfPi.compute n).hi <= 2 := by
  let stage : Nat := 64 * (n + 1)
  have hlower :=
    ArctanGeometry.arctanIntegralRectangleCompute_input_mul_kernel_le_lower
      (x := (1 : Rat)) (by native_decide) stage
  have hupper :=
    ArctanGeometry.arctanIntegralRectangleCompute_upper_le_input
      (x := (1 : Rat)) (by native_decide) stage
  change (1 : Rat) <=
      (SectorAreaReparametrization.angleOnUnitRegular.compute
        (1 : Rat) unitEndpoint n).lo /\
      (SectorAreaReparametrization.angleOnUnitRegular.compute
        (1 : Rat) unitEndpoint n).hi <= 2
  rw [SectorAreaReparametrization.angleOnUnitRegular_compute]
  simp only [QInterval.scaleRat, if_pos (by native_decide : (0 : Rat) <= 2)]
  change 1 <= 2 * (ArctanGeometry.arctanIntegralRectangleCompute 1 stage).lo /\
    2 * (ArctanGeometry.arctanIntegralRectangleCompute 1 stage).hi <= 2
  constructor
  · calc
      (1 : Rat) = 2 * (1 * ArctanGeometry.integralKernel 1) := by
        native_decide
      _ <= 2 * (ArctanGeometry.arctanIntegralRectangleCompute 1 stage).lo :=
        Rat.mul_le_mul_of_nonneg_left hlower (by native_decide)
  · calc
      2 * (ArctanGeometry.arctanIntegralRectangleCompute 1 stage).hi <=
          2 * 1 :=
        Rat.mul_le_mul_of_nonneg_left hupper (by native_decide)
      _ = 2 := by native_decide

/-- The accelerated sector clock has a stronger width modulus than the
factorial lift requires. -/
theorem halfPi_width_le_two_div_succ (n : Nat) :
    (halfPi.compute n).width <= 2 / (((n + 1 : Nat) : Rat)) := by
  have hclock :=
    SectorAreaReparametrization.angleOnUnitRegular_width_le
      (1 : Rat) unitEndpoint n
  have hdpos : 0 < ((n + 1 : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hinvnonneg : 0 <= (((n + 1 : Nat) : Rat)⁻¹) :=
    Rat.le_of_lt (Rat.inv_pos.2 hdpos)
  change (halfPi.compute n).width <= _ at hclock ⊢
  calc
    (halfPi.compute n).width <= 1 / (8 * ((n + 1 : Nat) : Rat)) := hclock
    _ = ((1 : Rat) / 8) * (((n + 1 : Nat) : Rat)⁻¹) := by
      calc
        (1 : Rat) / (8 * ((n + 1 : Nat) : Rat)) =
            (8 * ((n + 1 : Nat) : Rat))⁻¹ := by
          simp only [Rat.div_def, Rat.one_mul]
        _ = ((n + 1 : Nat) : Rat)⁻¹ * (8 : Rat)⁻¹ := by
          rw [Rat.inv_mul_rev]
        _ = (8 : Rat)⁻¹ * ((n + 1 : Nat) : Rat)⁻¹ := Rat.mul_comm _ _
        _ = ((1 : Rat) / 8) * (((n + 1 : Nat) : Rat)⁻¹) := by
          simp only [Rat.div_def, Rat.one_mul]
    _ <= 2 * (((n + 1 : Nat) : Rat)⁻¹) :=
      Rat.mul_le_mul_of_nonneg_right (by native_decide) hinvnonneg
    _ = 2 / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]

/-- The exact finite data consumed by the represented-angle factorial
rotation algorithm. -/
def halfPiInput : RotationLift.HalfPiInput where
  raw := halfPi
  valid := halfPi_valid
  bounds := halfPi_bounds
  width_le_two_div_succ := halfPi_width_le_two_div_succ

/-- The factorial rotation evaluated at the accelerated sector-area endpoint. -/
def rotation : ComplexRaw :=
  RotationLift.HalfPiInput.rotation halfPiInput

theorem rotation_valid : rotation.Valid := by
  simpa [rotation] using RotationLift.HalfPiInput.rotation_valid halfPiInput

/-- The sector-clock endpoint is the same raw angle as the independently
scheduled geometric half-pi presentation. -/
theorem halfPi_equiv_geometricHalfPi :
    halfPi.Equiv GeometricPiRotation.halfPi := by
  have hquarter :
      halfPi.Equiv
        (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)) := by
    simpa [halfPi, unitEndpoint] using
      SectorAreaReparametrization.regularAngleAt_one_equiv_quarterTurnRaw_one
  exact RealRaw.equiv_trans halfPi_valid
    GeometricPiRotation.geometricQuarterTurnOne_valid
    GeometricPiRotation.halfPi_valid hquarter
    (RealRaw.equiv_symm
      GeometricPiRotation.halfPi_equiv_geometricQuarterTurnOne)

/-- The full sector-area rectangle computation of pi: twice the certified
quarter-turn endpoint. -/
def piRaw : RealRaw :=
  (2 : Nat) * halfPi

theorem piRaw_valid : piRaw.Valid :=
  RealRaw.natScale_valid 2 halfPi_valid

/-- The endpoint's half-angle form is the literal doubled geometric
arctangent before it is transported through the geometry-only schedule. -/
theorem halfPi_equiv_twoArctanGeomOne :
    halfPi.Equiv ((2 : Nat) * ArctanGeometry.arctanGeom (1 : Rat)) := by
  simpa [halfPi, unitEndpoint] using
    SectorAreaReparametrization.regularAngleAt_equiv_two_arctanGeom
      (1 : Rat) unitEndpoint

/-- Doubling the accelerated sector endpoint agrees with the usual
four-times-geometric-arctangent pi raw.  The rebracketing is certified by
the positive rational-scaling law rather than by an ambient real-number
calculation. -/
theorem piRaw_equiv_fourArctanGeomOne :
    piRaw.Equiv ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat)) := by
  have hdouble :=
    RealRaw.natScale_equiv 2 halfPi_equiv_twoArctanGeomOne
  have hgeom : (ArctanGeometry.arctanGeom (1 : Rat)).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit (by native_decide) (by native_decide)
  have hcompose :
      ((2 : Nat) * ((2 : Nat) *
        ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) : RealRaw).Equiv
        ((4 : Nat) * ArctanGeometry.arctanGeom (1 : Rat) : RealRaw) := by
    have h := RealRaw.scaleRat_scaleRat_equiv_of_nonneg
      (2 : Rat) (2 : Rat) (by native_decide) (by native_decide)
      (ArctanGeometry.arctanGeom (1 : Rat)) hgeom
    have hscale (x : RealRaw) :
        ((2 : Nat) * x : RealRaw) = RealRaw.scaleRat 2 x := by
      rfl
    have hscale4 (x : RealRaw) :
        ((4 : Nat) * x : RealRaw) = RealRaw.scaleRat 4 x := by
      rfl
    rw [hscale, hscale, hscale4]
    simpa only [show (2 : Rat) * (2 : Rat) = 4 by native_decide] using h
  exact RealRaw.equiv_trans piRaw_valid
    (RealRaw.natScale_valid 2
      (RealRaw.natScale_valid 2 hgeom))
    (RealRaw.natScale_valid 4 hgeom)
    (by simpa [piRaw] using hdouble)
    hcompose

/-- The sector-clock presentation of the complex Euler input \(i\pi/2\). -/
def imaginaryHalf : ComplexRaw :=
  ComplexRaw.imaginaryAxis halfPi

theorem imaginaryHalf_valid : imaginaryHalf.Valid :=
  ComplexRaw.imaginaryAxis_valid halfPi_valid

/-- Embedding the sector endpoint on the imaginary axis preserves its
raw-angle agreement with the geometry-only Euler input. -/
theorem imaginaryHalf_equiv_geometricImaginaryHalf :
    imaginaryHalf.Equiv GeometricPiRotation.imaginaryHalf := by
  exact ComplexRaw.imaginaryAxis_equiv halfPi_valid
    GeometricPiRotation.halfPi_valid halfPi_equiv_geometricHalfPi

/-- The full stabilized factorial rotation respects the direct sector-area
endpoint identity.  This is a representative-level Euler-route bridge: the
remaining statement `rotation = i` is precisely the reparametrized
rotation-system uniqueness theorem, not an unproved change of pi inputs. -/
theorem rotation_equiv_geometricRotation :
    rotation.Equiv GeometricPiRotation.rotation := by
  simpa [rotation, halfPiInput, GeometricPiRotation.rotation,
    GeometricPiRotation.halfPiInput] using
    RotationLift.HalfPiInput.rotation_equiv_of_input_equiv
      halfPiInput GeometricPiRotation.halfPiInput
      halfPi_equiv_geometricHalfPi

end SectorAreaRotation

end ComputableAnalysis
