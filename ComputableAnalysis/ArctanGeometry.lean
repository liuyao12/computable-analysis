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
  piCircleAreaPolygon.innerBoundaryFrom (samplePoint y stage) k count

def innerBoundary (y : Rat) (stage : Nat) : List PiCirclePoint :=
  innerBoundaryFrom y stage 0 (stage + 1)

def outerBoundaryFrom (y : Rat) (stage k count : Nat) :
    List PiCirclePoint :=
  piCircleAreaPolygon.outerBoundaryFrom
    (samplePoint y stage) (outerTangentPoint y stage) k count

def outerBoundary (y : Rat) (stage : Nat) : List PiCirclePoint :=
  samplePoint y stage 0 :: outerBoundaryFrom y stage 0 stage

def twiceSignedAreaAux
    (first prev : PiCirclePoint) : List PiCirclePoint -> Rat
  | vertices => piCircleAreaPolygon.twiceSignedAreaAux pointCross first prev vertices

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

/-- Polygon-boundary scaffold for geometric arctangent on rational slopes.
The public computation below is the explicit rational update algorithm
`arctanGeom`; this version is retained for finite polygon comparison proofs. -/
def arctanGeomPolygon (x : Rat) : RealRaw :=
  if x = 0 then
    RealRaw.ofRat 0
  else if 0 <= x then
    positiveRaw x
  else
    -positiveRaw (-x)

theorem positiveComputeAtStage_eq_bounds
    (y : Rat) {s : Nat} (hs : s ≠ 0) :
    positiveComputeAtStage y s =
      { lo := innerSectorArea y s, hi := outerSectorArea y s } := by
  simp [positiveComputeAtStage, hs]

theorem positiveRaw_compute_eq_positiveComputeAtStage
    {y : Rat} (hy : y ≠ 0) (n : Nat) :
    (positiveRaw y).compute n = positiveComputeAtStage y (stage n) := by
  simp [positiveRaw, hy]

theorem arctanGeomPolygon_nonneg_compute_eq
    {x : Rat} (hx0 : x ≠ 0) (hx : 0 <= x) (n : Nat) :
    (arctanGeomPolygon x).compute n = positiveComputeAtStage x (stage n) := by
  simp [arctanGeomPolygon, positiveRaw, hx0, hx]

theorem arctanGeomPolygon_one_compute_eq (n : Nat) :
    (arctanGeomPolygon 1).compute n = positiveComputeAtStage 1 (stage n) := by
  have hnonzero : (1 : Rat) ≠ 0 := by native_decide
  have hnonneg : (0 : Rat) <= 1 := by native_decide
  exact arctanGeomPolygon_nonneg_compute_eq hnonzero hnonneg n

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

theorem arctanGeomPolygon_zero :
    arctanGeomPolygon 0 = RealRaw.ofRat 0 := by
  simp [arctanGeomPolygon]

/-- State for the update-loop presentation of geometric arctangent.  The
interval `[lo, hi]` stores current sector-area bounds, and `intervals` stores
the rational parameter intervals being refined. -/
structure AreaLoopState where
  lo : Rat
  hi : Rat
  intervals : List (Rat × Rat)
deriving Repr, DecidableEq

/-- The area added to the inscribed sector approximation when adjacent
parameters `p < q < r` replace the old interval `[p,r]` by two intervals. -/
def arctanAreaIncrement (p q r : Rat) : Rat :=
  (2 * (r - p) * (q - p) * (r - q)) /
    ((1 + p * p) * (1 + q * q) * (1 + r * r))

/-- The area removed from the outer tangent sector approximation when adjacent
parameters `p < q < r` replace the old interval `[p,r]` by two intervals. -/
def arctanAreaDecrement (p q r : Rat) : Rat :=
  ((r - p) * (q - p) * (r - q)) /
    ((1 + p * r) * (1 + p * q) * (1 + q * r))

namespace AreaLoopState

def refineAux : Rat -> Rat -> List (Rat × Rat) -> AreaLoopState
  | lo, hi, [] => { lo := lo, hi := hi, intervals := [] }
  | lo, hi, (p, r) :: rest =>
      let q := (p + r) / 2
      let next := refineAux
        (lo + arctanAreaIncrement p q r)
        (hi - arctanAreaDecrement p q r)
        rest
      { next with intervals := (p, q) :: (q, r) :: next.intervals }

end AreaLoopState

def refineAreaLoopState (state : AreaLoopState) : AreaLoopState :=
  AreaLoopState.refineAux state.lo state.hi state.intervals

def iterateAreaLoopState : Nat -> AreaLoopState -> AreaLoopState
  | 0, state => state
  | n + 1, state => iterateAreaLoopState n (refineAreaLoopState state)

def arctanAreaLoopInitial (x : Rat) : AreaLoopState :=
  { lo := x / (1 + x * x), hi := x, intervals := [(0, x)] }

def arctanAreaLoopState (x : Rat) (n : Nat) : AreaLoopState :=
  iterateAreaLoopState n (arctanAreaLoopInitial x)

def positiveLoopComputeAtStage (x : Rat) (n : Nat) : QInterval :=
  let state := arctanAreaLoopState x n
  { lo := state.lo, hi := state.hi }

def positiveLoopRaw (x : Rat) : RealRaw where
  compute := positiveLoopComputeAtStage x

/-- Geometric arctangent, presented as an explicit rational update algorithm.
This duplicates the exhaustion algorithm rather than factoring it through the
pi definition, so the later comparison theorem can relate two independent raw
objects. -/
def arctanGeom (x : Rat) : RealRaw :=
  if x = 0 then
    RealRaw.ofRat 0
  else if 0 <= x then
    positiveLoopRaw x
  else
    -positiveLoopRaw (-x)

theorem arctanAreaIncrement_eq_circleAreaIncrement (p m q : Rat) :
    arctanAreaIncrement p m q = circleAreaIncrement p m q := rfl

theorem arctanAreaDecrement_eq_circleAreaDecrement (p m q : Rat) :
    arctanAreaDecrement p m q = circleAreaDecrement p m q := rfl

theorem arctanGeom_nonneg_compute_eq
    {x : Rat} (hx0 : x ≠ 0) (hx : 0 <= x) (n : Nat) :
    (arctanGeom x).compute n = positiveLoopComputeAtStage x n := by
  simp [arctanGeom, positiveLoopRaw, hx0, hx]

theorem arctanGeom_one_compute_eq (n : Nat) :
    (arctanGeom 1).compute n = positiveLoopComputeAtStage 1 n := by
  have hnonzero : ¬(1 : Rat) = 0 := by native_decide
  have hnonneg : (0 : Rat) <= 1 := by native_decide
  exact arctanGeom_nonneg_compute_eq hnonzero hnonneg n

theorem arctanGeom_zero :
    arctanGeom 0 = RealRaw.ofRat 0 := by
  simp [arctanGeom]

def toPiAreaLoopState (state : AreaLoopState) : AreaBoundsLoopState :=
  { lo := state.lo, hi := state.hi, intervals := state.intervals }

theorem refineAux_toPiAreaLoopState
    (lo hi : Rat) (intervals : List (Rat × Rat)) :
    AreaBoundsLoopState.refineAux lo hi intervals =
      toPiAreaLoopState (AreaLoopState.refineAux lo hi intervals) := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaBoundsLoopState.refineAux, AreaLoopState.refineAux,
        toPiAreaLoopState]
  | cons pq rest ih =>
      rcases pq with ⟨p, r⟩
      let q := (p + r) / 2
      simp [AreaBoundsLoopState.refineAux, AreaLoopState.refineAux,
        toPiAreaLoopState, arctanAreaIncrement, circleAreaIncrement,
        arctanAreaDecrement, circleAreaDecrement]
      rw [ih]
      simp [toPiAreaLoopState]

theorem refineAreaBounds_toPiAreaLoopState (state : AreaLoopState) :
    refineAreaBounds (toPiAreaLoopState state) =
      toPiAreaLoopState (refineAreaLoopState state) := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_toPiAreaLoopState lo hi intervals

theorem iterateAreaBounds_toPiAreaLoopState (n : Nat)
    (state : AreaLoopState) :
    iterateAreaBounds n (toPiAreaLoopState state) =
      toPiAreaLoopState (iterateAreaLoopState n state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp [iterateAreaBounds, iterateAreaLoopState]
      rw [refineAreaBounds_toPiAreaLoopState]
      exact ih (refineAreaLoopState state)

theorem piCircleAreaInitial_eq_arctanAreaLoopInitial_one :
    piCircleAreaInitial =
      toPiAreaLoopState (arctanAreaLoopInitial 1) := by
  native_decide

theorem piCircleAreaState_eq_arctanAreaLoopState_one
    (n : Nat) :
    piCircleAreaState n =
      toPiAreaLoopState (arctanAreaLoopState 1 n) := by
  unfold piCircleAreaState arctanAreaLoopState
  rw [piCircleAreaInitial_eq_arctanAreaLoopInitial_one]
  exact iterateAreaBounds_toPiAreaLoopState n (arctanAreaLoopInitial 1)

/-- The comparison target saying that the loop definition of pi agrees stage by
stage with four times the geometric arctangent at `1`. -/
def PiAreaCompatibility : Prop :=
  forall n : Nat,
    (((4 : Nat) * arctanGeom (1 : Rat) : RealRaw).compute n) =
      piCircleArea.compute n

theorem piAreaCompatibility : PiAreaCompatibility := by
  intro n
  have hnonneg : (0 : Rat) <= 4 := by native_decide
  have hstate := piCircleAreaState_eq_arctanAreaLoopState_one n
  change (RealRaw.scaleRat (4 : Rat) (arctanGeom (1 : Rat))).compute n =
    piCircleArea.compute n
  simp [RealRaw.scaleRat, RealRaw.scaleRatCompute, hnonneg,
    arctanGeom_one_compute_eq, positiveLoopComputeAtStage,
    piCircleArea, piCircleAreaCompute, hstate,
    toPiAreaLoopState]

def functionRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => (arctanGeom x).compute

def representation : Elementary.Arctan.FunctionRepresentation where
  name := "arctan.geom"
  raw := functionRaw

def Valid : Prop :=
  forall x h, RealRaw.ValidCompute (functionRaw.compute x h)

def polygonFunctionRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => (arctanGeomPolygon x).compute

def polygonRepresentation : Elementary.Arctan.FunctionRepresentation where
  name := "arctan.geom.polygon"
  raw := polygonFunctionRaw

def PolygonValid : Prop :=
  forall x h, RealRaw.ValidCompute (polygonFunctionRaw.compute x h)

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
