import ComputableAnalysis.Elementary
import ComputableAnalysis.RationalCircle

/-!
# Geometric arctangent

This module keeps the geometric arctangent and its comparison-facing API
outside the rational-circle trigonometry module.  The rational-circle module
contains the circle stages, coordinate algorithms, and identity infrastructure;
comparison with other arctangent representations imports those extra
definitions here.
-/

namespace ComputableAnalysis

namespace ArctanGeometry

/-!
Geometric arctangent.

For rational `x`, the point
`((1 - x^2) / (1 + x^2), 2x / (1 + x^2))` lies on the unit circle at angle
`2 * arctan x`, so the unit-sector area from `0` to this parameter is
`arctan x`.
-/

def stage (n : Nat) : Nat :=
  2 ^ n

theorem stage_pos (n : Nat) : 0 < stage n := by
  unfold stage
  exact Nat.pow_pos (by omega : 0 < 2)

def parameter (y : Rat) (stage k : Nat) : Rat :=
  y * (k : Rat) / (stage : Rat)

def circlePoint (u : Rat) : PiCirclePoint :=
  let d := 1 + u * u
  { x := (1 - u * u) / d,
    y := (2 * u) / d }

def samplePoint (y : Rat) (stage k : Nat) : PiCirclePoint :=
  circlePoint (parameter y stage k)

def originPoint : PiCirclePoint :=
  { x := 0, y := 0 }

def pointCross (p q : PiCirclePoint) : Rat :=
  p.x * q.y - p.y * q.x

def tangentIntersection (p q : PiCirclePoint) : PiCirclePoint :=
  let det := pointCross p q
  { x := (q.y - p.y) / det,
    y := (p.x - q.x) / det }

def outerTangentPoint (y : Rat) (stage k : Nat) : PiCirclePoint :=
  tangentIntersection
    (samplePoint y stage k) (samplePoint y stage (k + 1))

def innerBoundaryFrom (y : Rat) (stage k count : Nat) :
    List PiCirclePoint :=
  piCircleArea.innerBoundaryFrom (samplePoint y stage) k count

def innerBoundary (y : Rat) (stage : Nat) : List PiCirclePoint :=
  innerBoundaryFrom y stage 0 (stage + 1)

def outerBoundaryFrom (y : Rat) (stage k count : Nat) :
    List PiCirclePoint :=
  piCircleArea.outerBoundaryFrom
    (samplePoint y stage) (outerTangentPoint y stage) k count

def outerBoundary (y : Rat) (stage : Nat) : List PiCirclePoint :=
  samplePoint y stage 0 :: outerBoundaryFrom y stage 0 stage

def twiceSignedAreaAux
    (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
  | vertices => piCircleArea.twiceSignedAreaAux pointCross first prev vertices

def twiceSignedArea : List PiCirclePoint -> Rat
  | [] => 0
  | first :: rest => twiceSignedAreaAux first first rest

def polygonArea (vertices : List PiCirclePoint) : Rat :=
  qabs (twiceSignedArea vertices / 2)

def innerSectorArea (y : Rat) (stage : Nat) : Rat :=
  polygonArea (originPoint :: innerBoundary y stage)

def outerSectorArea (y : Rat) (stage : Nat) : Rat :=
  polygonArea (originPoint :: outerBoundary y stage)

def positiveComputeAtStage (y : Rat) (stage : Nat) : QInterval :=
  if stage = 0 then
    { lo := 0, hi := 0 }
  else
    { lo := innerSectorArea y stage,
      hi := outerSectorArea y stage }

def positiveRaw (y : Rat) : RealRaw :=
  if y = 0 then
    RealRaw.ofRat 0
  else
    { compute := fun n => positiveComputeAtStage y (stage n) }

/-- Geometric arctangent on rational slopes. Positive inputs are sector
areas; negative inputs use oddness. -/
def arctanGeom (x : Rat) : RealRaw :=
  if x = 0 then
    RealRaw.ofRat 0
  else if 0 <= x then
    positiveRaw x
  else
    -positiveRaw (-x)

theorem circlePoint_zero :
    circlePoint 0 = ({ x := 1, y := 0 } : PiCirclePoint) := by
  native_decide

theorem samplePoint_zero (y : Rat) (stage : Nat) :
    samplePoint y stage 0 = ({ x := 1, y := 0 } : PiCirclePoint) := by
  unfold samplePoint parameter
  have hparam : y * ((0 : Nat) : Rat) / (stage : Rat) = 0 := by
    rw [show ((0 : Nat) : Rat) = 0 by rfl]
    rw [Rat.div_def]
    simp
  rw [hparam]
  exact circlePoint_zero

theorem samplePoint_self (y : Rat) (stage : Nat) (hstage : 0 < stage) :
    samplePoint y stage stage = circlePoint y := by
  unfold samplePoint parameter
  rw [show y * (stage : Rat) / (stage : Rat) = y by
    rw [Rat.div_def]
    have hne : (stage : Rat) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hstage
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]]

theorem positiveRaw_zero :
    positiveRaw 0 = RealRaw.ofRat 0 := by
  simp [positiveRaw]

theorem arctanGeom_zero :
    arctanGeom 0 = RealRaw.ofRat 0 := by
  simp [arctanGeom]

def functionRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => (arctanGeom x).compute

def representation : Elementary.Arctan.FunctionRepresentation where
  name := "arctan.geom"
  raw := functionRaw

def Valid : Prop :=
  forall x h, RealRaw.ValidCompute (functionRaw.compute x h)

def PowerSeriesAgreesOnUnit : Prop :=
  Elementary.Arctan.Equivalent Elementary.Arctan.powerSeries representation

theorem powerSeries_equiv_geometric_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctan x).Equiv (arctanGeom x) := by
  have hgeom : representation.raw.definedAt x := by
    simp [representation, functionRaw]
  simpa [Elementary.Arctan.powerSeries, representation, functionRaw,
    Elementary.Arctan.powerSeriesFunctionRaw, PartialRealFunRaw.AgreeOnOverlap,
    RealRaw.Equiv] using h x hx hgeom

theorem geometric_equiv_powerSeries_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctanGeom x).Equiv (arctan x) :=
  RealRaw.equiv_symm
    (powerSeries_equiv_geometric_of_agreement h hx)

end ArctanGeometry

end ComputableAnalysis
