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
