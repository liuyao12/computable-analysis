import ComputableAnalysis.IntegralIdentities

/-!
# Lightweight scheduled arctangent representation

This module exposes the rescheduled rectangle computation without importing
the more expensive interval-regularity and inverse-search certificate.  The
two layers are intentionally separate: a user may consume the raw evaluator
and its equivalence proof before supplying the additional uniform witnesses
needed by an inverse theorem.
-/

namespace ComputableAnalysis

def arctanScheduledCoreStage (n : Nat) : Nat := 64 * (n + 1)

def arctanScheduledCoreSchedule : RealRaw.StageSchedule where
  stage := arctanScheduledCoreStage
  monotone := by
    intro i j hij
    dsimp [arctanScheduledCoreStage]
    omega
  cofinal := by
    intro target
    refine ⟨target, ?_⟩
    dsimp [arctanScheduledCoreStage]
    omega

def arctanScheduledCoreRaw (x : Rat) : RealRaw where
  compute := fun n =>
    ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledCoreStage n)

theorem arctanScheduledCoreRaw_eq_schedule (x : Rat) :
    arctanScheduledCoreRaw x =
      RealRaw.schedule arctanScheduledCoreSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x) := by
  rfl

theorem arctanScheduledCoreRaw_valid
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanScheduledCoreRaw x).Valid := by
  rw [arctanScheduledCoreRaw_eq_schedule]
  exact RealRaw.schedule_valid
    (ArctanGeometry.arctanIntegralRectangleRaw x)
    (ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1)
    arctanScheduledCoreSchedule

theorem arctanScheduledCoreRaw_equiv_arctanGeom
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanScheduledCoreRaw x).Equiv
      (ArctanGeometry.arctanGeom x) := by
  rw [arctanScheduledCoreRaw_eq_schedule]
  have hraw :
      (ArctanGeometry.arctanIntegralRectangleRaw x).Valid :=
    ArctanGeometry.arctanIntegralRectangleRaw_valid hx0 hx1
  have hscheduled :
      (RealRaw.schedule arctanScheduledCoreSchedule
        (ArctanGeometry.arctanIntegralRectangleRaw x)).Valid :=
    RealRaw.schedule_valid _ hraw arctanScheduledCoreSchedule
  have hgeom : (ArctanGeometry.arctanGeom x).Valid :=
    ArctanGeometry.arctanGeom_valid_on_unit hx0 hx1
  exact RealRaw.equiv_trans hscheduled hraw hgeom
    (RealRaw.equiv_symm (RealRaw.schedule_equiv _ hraw
      arctanScheduledCoreSchedule))
    (ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom hx0)

theorem arctanScheduledCoreRaw_width_le
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    ((arctanScheduledCoreRaw x).compute n).width <=
      1 / (((16 * (n + 1) : Nat) : Rat)) := by
  change (ArctanGeometry.arctanIntegralRectangleCompute x
      (arctanScheduledCoreStage n)).width <=
    1 / (((16 * (n + 1) : Nat) : Rat))
  have h := ArctanGeometry.arctanIntegralRectangleCompute_width_le_four_div_succ
    hx0 hx1 (arctanScheduledCoreStage n)
  have hmain :
      (4 : Rat) / (((arctanScheduledCoreStage n + 1 : Nat) : Rat)) <=
        1 / (((16 * (n + 1) : Nat) : Rat)) := by
    apply Rat.le_of_mul_le_mul_right
      (c := ((arctanScheduledCoreStage n + 1 : Nat) : Rat) *
        ((16 * (n + 1) : Nat) : Rat))
    · rw [Rat.div_def, Rat.div_def]
      dsimp [arctanScheduledCoreStage]
      have hn : ((n + 1 : Nat) : Rat) ≠ 0 := by
        exact Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega))
      grind [Rat.natCast_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]
    · have hN : 0 < ((arctanScheduledCoreStage n + 1 : Nat) : Rat) := by
        exact (Rat.natCast_pos).2 (by dsimp [arctanScheduledCoreStage]; omega)
      have h16 : 0 < ((16 * (n + 1) : Nat) : Rat) := by
        exact (Rat.natCast_pos).2 (by omega)
      exact Rat.mul_pos hN h16
  exact Rat.le_trans h hmain

end ComputableAnalysis
