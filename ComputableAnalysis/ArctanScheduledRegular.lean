import ComputableAnalysis.IntegralIdentities

/-!
# A scheduled interval-regular arctangent branch

The geometric arctangent raw already has the desired mathematical meaning, but
its native rectangle evaluator uses a fixed finite stage schedule.  This file
packages a rescheduled version whose output precision is chosen from the
requested interval precision.  It is a separate representation; a later
equivalence theorem can transport inverse-search results to the geometric raw.
-/

namespace ComputableAnalysis

def arctanScheduledStage (n : Nat) : Nat := 64 * (n + 1)

def arctanScheduledStageSchedule : RealRaw.StageSchedule where
  stage := arctanScheduledStage
  monotone := by
    intro i j hij
    dsimp [arctanScheduledStage]
    omega
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    dsimp [arctanScheduledStage]
    omega

def arctanScheduledRectangleRaw (x : Rat) : RealRaw where
  compute := fun n =>
    ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledStage n)

theorem arctanScheduledRectangleRaw_eq_schedule (x : Rat) :
    arctanScheduledRectangleRaw x =
      RealRaw.schedule arctanScheduledStageSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x) := by
  rfl

theorem arctanScheduledRectangleRaw_valid
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanScheduledRectangleRaw x).Valid := by
  rw [arctanScheduledRectangleRaw_eq_schedule]
  exact RealRaw.schedule_valid
    (ArctanGeometry.arctanIntegralRectangleRaw x)
    (ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1)
    arctanScheduledStageSchedule

theorem arctanScheduledRectangleRaw_equiv_arctanGeom
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanScheduledRectangleRaw x).Equiv
      (ArctanGeometry.arctanGeom x) := by
  rw [arctanScheduledRectangleRaw_eq_schedule]
  have hraw :
      (ArctanGeometry.arctanIntegralRectangleRaw x).Valid :=
    ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1
  have hscheduled :
      (RealRaw.schedule arctanScheduledStageSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x)).Valid :=
    RealRaw.schedule_valid _ hraw arctanScheduledStageSchedule
  have hgeom : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1
  exact RealRaw.equiv_trans hscheduled hraw hgeom
    (RealRaw.equiv_symm (RealRaw.schedule_equiv _ hraw
      arctanScheduledStageSchedule))
    (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom hx0)

def arctanScheduledRectangleOnUnit : FunctionOnInterval where
  raw := {
    definedAt := fun x => 0 <= x ∧ x <= 1
    compute := fun x _hx n =>
      ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanScheduledStage n)
    rate := fun _ _ => .unknown
  }
  lower := 0
  upper := 1
  defined_on := fun _ hx => hx
  valid_on := by
    intro x hx
    change RealRaw.ValidCompute
      (fun n => ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanScheduledStage n))
    constructor
    · intro n
      exact ArctanGeometry.arctanIntegralRectangleCompute_ordered hx.1
        (arctanScheduledStage n)
    constructor
    · intro n m hnm
      have hstage : arctanScheduledStage n <= arctanScheduledStage m := by
        dsimp [arctanScheduledStage]
        omega
      exact ArctanGeometry.arctanIntegralRectangleCompute_nested
        hx.1 (arctanScheduledStage n) (arctanScheduledStage m) hstage
    · intro eps
      obtain ⟨N, hN⟩ :=
        ArctanGeometry.arctanIntegralRectangleCompute_widthsShrink
          hx.1 hx.2 eps
      refine ⟨N, ?_⟩
      intro n hn
      have hstageN : N <= arctanScheduledStage n := by
        dsimp [arctanScheduledStage]
        omega
      exact hN (arctanScheduledStage n) hstageN

theorem arctanScheduledRectangleOnUnit_compute_eq
    (x : Rat) (hx : inDomainInterval 0 1 x) (n : Nat) :
    arctanScheduledRectangleOnUnit.compute x hx n =
      ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanScheduledStage n) := by
  rfl

theorem arctanScheduledRectangleOnUnit_width_le
    (x : Rat) (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanScheduledRectangleOnUnit.compute x
      ⟨hx0, hx1⟩ n).width <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
  change (ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledStage n)).width <=
    1 / (((16 * (n + 1) : Nat) : Rat))
  have h := ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
    hx0 hx1 (arctanScheduledStage n)
  have hmain :
      (4 : Rat) / (((arctanScheduledStage n + 1 : Nat) : Rat)) <=
        1 / (((16 * (n + 1) : Nat) : Rat)) := by
    apply Rat.le_of_mul_le_mul_right
      (c := ((arctanScheduledStage n + 1 : Nat) : Rat) *
        ((16 * (n + 1) : Nat) : Rat))
    · rw [Rat.div_def, Rat.div_def]
      dsimp [arctanScheduledStage]
      have hn : ((n + 1 : Nat) : Rat) ≠ 0 := by
        exact Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega))
      grind [Rat.natCast_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]
    · have hN : 0 < ((arctanScheduledStage n + 1 : Nat) : Rat) := by
        exact (Rat.natCast_pos).2 (by dsimp [arctanScheduledStage]; omega)
      have h16 : 0 < ((16 * (n + 1) : Nat) : Rat) := by
        exact (Rat.natCast_pos).2 (by omega)
      exact Rat.mul_pos hN h16
  exact Rat.le_trans h hmain

theorem arctanScheduledRectangleOnUnit_nondecreasing :
    NondecreasingOnInterval arctanScheduledRectangleOnUnit := by
  intro x y hx hy hxy n
  change
    (ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledStage n)).lo <=
      (ArctanGeometry.arctanIntegralRectangleCompute y
        (arctanScheduledStage n)).hi
  exact ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
    hx.1 hxy (arctanScheduledStage n)

def arctanScheduledRectangleOnUnit_monotone :
    MonotoneOnInterval arctanScheduledRectangleOnUnit :=
  MonotoneOnInterval.ofNondecreasing
    arctanScheduledRectangleOnUnit_nondecreasing

def arctanScheduledRectangleOnUnit_effectiveInverseSeparation :
    EffectiveInverseSeparation arctanScheduledRectangleOnUnit where
  kind := .nondecreasing
  inputPrecision := fun n => n + 1
  inputPrecision_pos := fun n => Nat.succ_pos n
  outputPrecision := fun n => n
  separated := by
    intro x y hx hy n hsep
    change
      (ArctanGeometry.arctanIntegralRectangleCompute x
        (arctanScheduledStage n)).hi <
      (ArctanGeometry.arctanIntegralRectangleCompute y
          (arctanScheduledStage n)).lo
    exact ArctanGeometry.arctanIntegralRectangleCompute_boxes_strictly_separated
      hx.1 hx.2 hy.1 hy.2 n hsep

end ComputableAnalysis
