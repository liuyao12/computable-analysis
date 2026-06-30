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

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d := by
  grind

private theorem one_div_le_one_div_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : Not (a = 0) := Rat.ne_of_gt ha
  have hbne : Not (b = 0) := Rat.ne_of_gt hb
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  refine Rat.le_of_mul_le_mul_right (c := a * b) ?_ habpos
  calc
    (1 / b) * (a * b) = a := by
      rw [Rat.div_def]
      have hcancel : b * Inv.inv b = 1 := Rat.mul_inv_cancel b hbne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= b := hab
    _ = (1 / a) * (a * b) := by
      rw [Rat.div_def]
      have hcancel : a * Inv.inv a = 1 := Rat.mul_inv_cancel a hane
      grind [Rat.mul_assoc, Rat.mul_comm]

/-!
The following cell formulas are the finite comparison layer between the
geometric arctangent and the definite integral of `1 / (1 + u^2)`.  No area
axiom or derivative theorem is used here: everything is a rational inequality
on one cell, then a finite sum over cells.
-/

/-- The exact decreasing kernel whose lower/upper rectangle sums compute
arctangent. -/
def integralKernel (u : Rat) : Rat :=
  1 / (1 + u * u)

/-- Lower rectangle on `[p,r]` for `1/(1+u^2)`, valid on nonnegative cells. -/
def integralLowerStep (p r : Rat) : Rat :=
  (r - p) * integralKernel r

/-- Upper rectangle on `[p,r]` for `1/(1+u^2)`, valid on nonnegative cells. -/
def integralUpperStep (p r : Rat) : Rat :=
  (r - p) * integralKernel p

/-- Inscribed geometric sector cell between rational parameters `p` and `r`. -/
def geometricLowerStep (p r : Rat) : Rat :=
  ((r - p) * (1 + p * r)) /
    ((1 + p * p) * (1 + r * r))

/-- Circumscribed tangent-sector cell between rational parameters `p` and `r`. -/
def geometricUpperStep (p r : Rat) : Rat :=
  (r - p) / (1 + p * r)

def integralCellInterval (p r : Rat) : QInterval :=
  { lo := integralLowerStep p r, hi := integralUpperStep p r }

def geometricCellInterval (p r : Rat) : QInterval :=
  { lo := geometricLowerStep p r, hi := geometricUpperStep p r }

private theorem left_square_le_factor {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    1 + p * p <= 1 + p * r := by
  have hmul : p * p <= p * r :=
    Rat.mul_le_mul_of_nonneg_left hpr hp0
  grind

private theorem factor_le_right_square {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    1 + p * r <= 1 + r * r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hmul : p * r <= r * r :=
    Rat.mul_le_mul_of_nonneg_right hpr hr0
  grind

theorem integralLowerStep_le_geometricLowerStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    integralLowerStep p r <= geometricLowerStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hfac : 1 + p * p <= 1 + p * r :=
    left_square_le_factor hp0 hpr
  have hmain : (r - p) * (1 + p * p) <= (r - p) * (1 + p * r) :=
    Rat.mul_le_mul_of_nonneg_left hfac hlen
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hrdenpos : 0 < 1 + r * r :=
    RationalCircle.Stage.one_add_square_pos r
  have hrdenne : 1 + r * r ≠ 0 := Rat.ne_of_gt hrdenpos
  have hdenpos : 0 < (1 + p * p) * (1 + r * r) :=
    Rat.mul_pos hpdenpos hrdenpos
  refine Rat.le_of_mul_le_mul_right
    (c := (1 + p * p) * (1 + r * r)) ?_ hdenpos
  unfold integralLowerStep geometricLowerStep integralKernel
  calc
    ((r - p) * (1 / (1 + r * r))) *
        ((1 + p * p) * (1 + r * r))
        = (r - p) * (1 + p * p) := by
          rw [Rat.div_def]
          have hcancel : (1 + r * r) * (1 + r * r)⁻¹ = 1 :=
            Rat.mul_inv_cancel _ hrdenne
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) * (1 + p * r) := hmain
    _ = (((r - p) * (1 + p * r)) /
        ((1 + p * p) * (1 + r * r))) *
        ((1 + p * p) * (1 + r * r)) := by
          rw [Rat.div_def]
          have hcancel : ((1 + p * p) * (1 + r * r)) *
              (((1 + p * p) * (1 + r * r))⁻¹) = 1 :=
            Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenpos)
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem integralLowerStep_le_geometricUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    integralLowerStep p r <= geometricUpperStep p r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hprpos : 0 < 1 + p * r :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  have hfac : 1 + p * r <= 1 + r * r :=
    factor_le_right_square hp0 hpr
  have hinv : 1 / (1 + r * r) <= 1 / (1 + p * r) :=
    one_div_le_one_div_of_pos_of_le hprpos hfac
  unfold integralLowerStep geometricUpperStep integralKernel
  repeat rw [Rat.div_def] at hinv ⊢
  simpa [Rat.mul_assoc] using Rat.mul_le_mul_of_nonneg_left hinv hlen

theorem geometricLowerStep_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    geometricLowerStep p r <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hfac : 1 + p * r <= 1 + r * r :=
    factor_le_right_square hp0 hpr
  have hmain : (r - p) * (1 + p * r) <= (r - p) * (1 + r * r) :=
    Rat.mul_le_mul_of_nonneg_left hfac hlen
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hrdenpos : 0 < 1 + r * r :=
    RationalCircle.Stage.one_add_square_pos r
  have hpdenne : 1 + p * p ≠ 0 := Rat.ne_of_gt hpdenpos
  have hdenpos : 0 < (1 + p * p) * (1 + r * r) :=
    Rat.mul_pos hpdenpos hrdenpos
  refine Rat.le_of_mul_le_mul_right
    (c := (1 + p * p) * (1 + r * r)) ?_ hdenpos
  unfold geometricLowerStep integralUpperStep integralKernel
  calc
    (((r - p) * (1 + p * r)) /
        ((1 + p * p) * (1 + r * r))) *
        ((1 + p * p) * (1 + r * r))
        = (r - p) * (1 + p * r) := by
          rw [Rat.div_def]
          have hcancel : ((1 + p * p) * (1 + r * r)) *
              (((1 + p * p) * (1 + r * r))⁻¹) = 1 :=
            Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenpos)
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) * (1 + r * r) := hmain
    _ = ((r - p) * (1 / (1 + p * p))) *
        ((1 + p * p) * (1 + r * r)) := by
          rw [Rat.div_def]
          have hcancel : (1 + p * p) * (1 + p * p)⁻¹ = 1 :=
            Rat.mul_inv_cancel _ hpdenne
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem geometricUpperStep_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    geometricUpperStep p r <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hfac : 1 + p * p <= 1 + p * r :=
    left_square_le_factor hp0 hpr
  have hinv : 1 / (1 + p * r) <= 1 / (1 + p * p) :=
    one_div_le_one_div_of_pos_of_le hpdenpos hfac
  unfold geometricUpperStep integralUpperStep integralKernel
  repeat rw [Rat.div_def] at hinv ⊢
  simpa [Rat.mul_assoc] using Rat.mul_le_mul_of_nonneg_left hinv hlen

theorem integralCellInterval_contains_geometricCellInterval
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    (integralCellInterval p r).ContainsInterval
      (geometricCellInterval p r) := by
  unfold QInterval.ContainsInterval integralCellInterval geometricCellInterval
  exact ⟨integralLowerStep_le_geometricLowerStep hp0 hpr,
    geometricUpperStep_le_integralUpperStep hp0 hpr⟩

theorem integralCellInterval_overlaps_geometricCellInterval
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    QInterval.Overlaps (integralCellInterval p r)
      (geometricCellInterval p r) := by
  unfold QInterval.Overlaps integralCellInterval geometricCellInterval
  exact ⟨integralLowerStep_le_geometricUpperStep hp0 hpr,
    geometricLowerStep_le_integralUpperStep hp0 hpr⟩

/-- A finite partition whose cells lie in the nonnegative half-line. -/
def NonnegativeIntervals : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      0 <= p /\ p <= r /\ NonnegativeIntervals rest

def integralLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => integralLowerStep p r + integralLowerSum rest

def integralUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => integralUpperStep p r + integralUpperSum rest

def geometricLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => geometricLowerStep p r + geometricLowerSum rest

def geometricUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => geometricUpperStep p r + geometricUpperSum rest

def integralSumInterval (intervals : List (Rat × Rat)) : QInterval :=
  { lo := integralLowerSum intervals, hi := integralUpperSum intervals }

def geometricSumInterval (intervals : List (Rat × Rat)) : QInterval :=
  { lo := geometricLowerSum intervals, hi := geometricUpperSum intervals }

theorem integralLowerSum_le_geometricLowerSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <= geometricLowerSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum, geometricLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [integralLowerSum, geometricLowerSum]
      exact rat_add_le_add
        (integralLowerStep_le_geometricLowerStep hp0 hpr)
        (ih hrest)

theorem integralLowerSum_le_geometricUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <= geometricUpperSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum, geometricUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [integralLowerSum, geometricUpperSum]
      exact rat_add_le_add
        (integralLowerStep_le_geometricUpperStep hp0 hpr)
        (ih hrest)

theorem geometricLowerSum_le_integralUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    geometricLowerSum intervals <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricLowerSum, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricLowerSum, integralUpperSum]
      exact rat_add_le_add
        (geometricLowerStep_le_integralUpperStep hp0 hpr)
        (ih hrest)

theorem geometricUpperSum_le_integralUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    geometricUpperSum intervals <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricUpperSum, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricUpperSum, integralUpperSum]
      exact rat_add_le_add
        (geometricUpperStep_le_integralUpperStep hp0 hpr)
        (ih hrest)

theorem integralSumInterval_contains_geometricSumInterval
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    (integralSumInterval intervals).ContainsInterval
      (geometricSumInterval intervals) := by
  unfold QInterval.ContainsInterval integralSumInterval geometricSumInterval
  exact ⟨integralLowerSum_le_geometricLowerSum intervals hwf,
    geometricUpperSum_le_integralUpperSum intervals hwf⟩

theorem integralSumInterval_overlaps_geometricSumInterval
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    QInterval.Overlaps (integralSumInterval intervals)
      (geometricSumInterval intervals) := by
  unfold QInterval.Overlaps integralSumInterval geometricSumInterval
  exact ⟨integralLowerSum_le_geometricUpperSum intervals hwf,
    geometricLowerSum_le_integralUpperSum intervals hwf⟩

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
