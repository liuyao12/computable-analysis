import ComputableAnalysis.IntegralIdentities

/-!
# Inverse-search data for the geometric arctangent

The geometric arctangent is represented here by its certified rectangle
evaluator.  This is the computable monotone branch used for inverse search:
all values remain rational interval boxes, and its finite order and strict
separation certificates are already available without completed reals.
-/

namespace ComputableAnalysis

open ArctanGeometry
open IntegralIdentities

namespace ArctanGeomInverseData

abbrev arctanGeomOnUnit : FunctionOnInterval :=
  IntegralIdentities.arctanIntegralRectangleOnUnit

private theorem arctanGeom_compute_eq_positiveLoop
    {x : Rat} (hx0 : 0 <= x) (n : Nat) :
    (arctanGeom x).compute n = positiveLoopComputeAtStage x n := by
  by_cases hzero : x = 0
  · subst x
    rw [positiveLoopComputeAtStage_zero]
    simp [arctanGeom]
  · exact arctanGeom_nonneg_compute_eq hzero hx0 n

private theorem arctanGeom_compute_contained_in_rectangle
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    QInterval.ContainsInterval
      (arctanIntegralRectangleCompute x n)
      ((arctanGeom x).compute n) := by
  rw [arctanGeom_compute_eq_positiveLoop hx0 n]
  exact arctanAreaLoop_integralSum_contains_positiveLoop hx0 n

theorem arctanGeomOnUnit_nondecreasing :
    NondecreasingOnInterval arctanGeomOnUnit := by
  exact IntegralIdentities.arctanIntegralRectangleOnUnit_nondecreasing

def arctanGeomOnUnit_monotone :
    MonotoneOnInterval arctanGeomOnUnit :=
  MonotoneOnInterval.ofNondecreasing arctanGeomOnUnit_nondecreasing

/-! The rectangle branch supplies the explicit near-continuity estimate.  This
is the finite regularity datum needed before assembling the full
interval-regular inverse branch. -/

theorem arctanGeomOnUnit_near_of_qabs_le
    (eps : QPos) (n : Nat) (hn : 4 * (eps.val.den + 1) <= n)
    {x y : Rat}
    (hx : inDomainInterval arctanGeomOnUnit.lower
      arctanGeomOnUnit.upper x)
    (hy : inDomainInterval arctanGeomOnUnit.lower
      arctanGeomOnUnit.upper y)
    (hclose : qabs (y - x) <= eps.val) :
    QInterval.NearAt
      (arctanGeomOnUnit.compute x hx n)
      (arctanGeomOnUnit.compute y hy n) eps := by
  exact IntegralIdentities.arctanIntegralRectangleOnUnit_near_of_qabs_le
    eps n hn hx hy hclose

def arctanGeomOnUnit_effectiveModulus :
    EffectiveModulusFor arctanGeomOnUnit :=
  IntegralIdentities.arctanIntegralRectangleOnUnit_effectiveModulus

/-! The interval-regularity interface asks for the literal width budget
`1/(n+1)`.  Expose the rectangle evaluator with an explicit cofinal schedule
so its native `4/(stage+1)` budget fits that interface. -/

def arctanGeomScheduledStage (n : Nat) : Nat := 4 * (n + 1)

def arctanGeomScheduledStageSchedule : RealRaw.StageSchedule where
  stage := arctanGeomScheduledStage
  monotone := by
    intro i j hij
    dsimp [arctanGeomScheduledStage]
    omega
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    dsimp [arctanGeomScheduledStage]
    omega

def arctanGeomScheduledOnUnit : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x ∧ x <= 1
    compute := fun x _hx n =>
      ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanGeomScheduledStage n)
    rate := fun _x _hx => .unknown }
  lower := 0
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    have hraw := ArctanGeometry.arctanIntegralRectangleRaw_valid hx.1 hx.2
    have hs := RealRaw.schedule_valid
      (ArctanGeometry.arctanIntegralRectangleRaw x) hraw
      arctanGeomScheduledStageSchedule
    change RealRaw.ValidCompute
      (fun n => ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanGeomScheduledStage n)) at hs
    exact hs

theorem arctanGeomScheduledOnUnit_compute_eq
    (x : Rat) (hx : inDomainInterval
      arctanGeomScheduledOnUnit.lower arctanGeomScheduledOnUnit.upper x)
  (n : Nat) :
    arctanGeomScheduledOnUnit.compute x hx n =
      ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanGeomScheduledStage n) := by
  rfl

theorem arctanGeomScheduledOnUnit_width_le
    (x : Rat) (hx : inDomainInterval
      arctanGeomScheduledOnUnit.lower arctanGeomScheduledOnUnit.upper x)
    (n : Nat) :
    (arctanGeomScheduledOnUnit.compute x hx n).width <=
  1 / (((n + 1 : Nat) : Rat)) := by
  rw [arctanGeomScheduledOnUnit_compute_eq]
  have h := ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
    hx.1 hx.2 (arctanGeomScheduledStage n)
  have hden_le : 4 * (n + 1) <= 4 * (n + 1) + 1 := Nat.le_succ _
  have hrecip :
      1 / (((4 * (n + 1) + 1 : Nat) : Rat)) <=
        1 / (((4 * (n + 1) : Nat) : Rat)) :=
    FTC.one_div_nat_antitone
      (by omega : 0 < 4 * (n + 1))
      (by omega : 0 < 4 * (n + 1) + 1) hden_le
  calc
    (arctanGeomScheduledOnUnit.compute x hx n).width <=
        4 / (((arctanGeomScheduledStage n + 1 : Nat) : Rat)) := h
    _ = 4 * (1 / (((4 * (n + 1) + 1 : Nat) : Rat))) := by
      change 4 / (((4 * (n + 1) + 1 : Nat) : Rat)) = _
      rw [Rat.div_def]
      grind [Rat.mul_assoc]
    _ <= 4 * (1 / (((4 * (n + 1) : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hrecip (by native_decide)
    _ = 1 / (((n + 1 : Nat) : Rat)) := by
      repeat rw [Rat.div_def]
      rw [Rat.natCast_mul]
      have hscale : (4 : Rat) * (4 : Rat)⁻¹ = (1 : Rat) := by
        native_decide
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem arctanGeomScheduled_forward_lower_sub_upper_le
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat) :
    (arctanGeomScheduledOnUnit.compute (x + h)
      ⟨by change 0 <= x + h; grind, hupper⟩ n).lo -
    (arctanGeomScheduledOnUnit.compute x ⟨hx0, hx1⟩ n).hi <=
      h + 1 / (((n + 1 : Nat) : Rat) / 4) := by
  let S := arctanGeomScheduledStage n
  have hrect :=
    ArctanGeometry.arctanIntegralRectangleCompute_forward_lower_sub_upper_le_step
      hx0 hx1 hpos hupper S
  have hrectWidthX :=
    ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
      hx0 hx1 S
  have hrectWidthY :=
    ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
      (by grind) hupper S
  change (ArctanGeometry.arctanIntegralRectangleCompute (x + h) S).lo -
      (ArctanGeometry.arctanIntegralRectangleCompute x S).hi <= _
  unfold QInterval.width at hrectWidthX hrectWidthY
  have hrectlo :
      (ArctanGeometry.arctanIntegralRectangleCompute (x + h) S).lo -
          (ArctanGeometry.arctanIntegralRectangleCompute x S).hi <= h := hrect
  have hnpos : 0 < ((n + 1 : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hdenpos : 0 < ((n + 1 : Nat) : Rat) / 4 := by
    rw [Rat.div_def]
    exact Rat.mul_pos hnpos (by native_decide)
  have hbudget : 0 <= 1 / (((n + 1 : Nat) : Rat) / 4) := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
  exact Rat.le_trans hrectlo (by grind)

def arctanGeomScheduledImage
    (I : QInterval)
    (hI : subintervalOf I arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper)
    (n : Nat) : QInterval :=
  let hLo : inDomainInterval arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper I.lo :=
    ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
  let hHi : inDomainInterval arctanGeomScheduledOnUnit.lower
      arctanGeomScheduledOnUnit.upper I.hi :=
    ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
  let budget : Rat := 1 / (8 * ((n + 1 : Nat) : Rat))
  { lo := (arctanGeomScheduledOnUnit.compute I.lo hLo n).lo - budget,
    hi := (arctanGeomScheduledOnUnit.compute I.hi hHi n).hi + budget }

/-! The geometric inverse branch uses the rectangle evaluator's effective
strict separation certificate. -/

def arctanGeomOnUnit_effectiveInverseSeparation :
    EffectiveInverseSeparation arctanGeomOnUnit :=
  IntegralIdentities.arctanIntegralRectangleOnUnit_effectiveInverseSeparation

end ArctanGeomInverseData
end ComputableAnalysis
