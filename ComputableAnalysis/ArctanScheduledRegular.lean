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

/-! The endpoint-expanded image of a small cell is the interval-level
regularity witness.  This helper isolates the finite width arithmetic from the
record constructor below, which keeps dependent domain proofs out of the main
calculation. -/

set_option maxHeartbeats 5000000 in
theorem arctanScheduledRectangleOnUnit_endpointImage_width_le
    (I : QInterval) (hI : subintervalOf I 0 1) (n : Nat)
    (hLo : inDomainInterval 0 1 I.lo)
    (hHi : inDomainInterval 0 1 I.hi)
    (hsmall : I.width <= 1 / (((2 * (n + 1) : Nat) : Rat)))
    (hpos : 0 < I.hi - I.lo) :
    let J : QInterval :=
      { lo := (arctanScheduledRectangleOnUnit.compute I.lo hLo n).lo
        hi := (arctanScheduledRectangleOnUnit.compute I.hi hHi n).hi }
    0 <= J.width /\ J.width <= 1 / (((n + 1 : Nat) : Rat)) := by
  have hstep : I.hi - I.lo <=
      1 / (((2 * (n + 1) : Nat) : Rat)) := by
    simpa [QInterval.width] using hsmall
  have hNpos : 0 < ((n + 1 : Nat) : Rat) :=
    (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hboxLo := arctanScheduledRectangleOnUnit_width_le I.lo hLo.1 hLo.2 n
  have hboxHi := arctanScheduledRectangleOnUnit_width_le I.hi hHi.1 hHi.2 n
  have hforward :=
    ArctanGeometry.arctanIntegralRectangleCompute_forward_lower_sub_upper_le_step
      hI.1 hLo.2 hpos (by
        rw [show I.lo + (I.hi - I.lo) = I.hi by grind]
        exact hI.2.2)
      (arctanScheduledStage n)
  dsimp
  change
    0 <=
        (arctanScheduledRectangleOnUnit.compute I.hi hHi n).hi -
          (arctanScheduledRectangleOnUnit.compute I.lo hLo n).lo /\
      (arctanScheduledRectangleOnUnit.compute I.hi hHi n).hi -
          (arctanScheduledRectangleOnUnit.compute I.lo hLo n).lo <=
        1 / (((n + 1 : Nat) : Rat))
  change
    (ArctanGeometry.arctanIntegralRectangleCompute I.hi
        (arctanScheduledStage n)).lo -
        (ArctanGeometry.arctanIntegralRectangleCompute I.lo
          (arctanScheduledStage n)).hi <= I.hi - I.lo at hforward
  change 0 <=
    (ArctanGeometry.arctanIntegralRectangleCompute I.hi
        (arctanScheduledStage n)).hi -
      (ArctanGeometry.arctanIntegralRectangleCompute I.lo
        (arctanScheduledStage n)).lo /\
    _ <= _
  have hLoOrder :=
    ArctanGeometry.arctanIntegralRectangleCompute_ordered hLo.1
      (arctanScheduledStage n)
  have hHiOrder :=
    ArctanGeometry.arctanIntegralRectangleCompute_ordered hHi.1
      (arctanScheduledStage n)
  unfold QInterval.width at hboxLo hboxHi ⊢
  constructor
  · grind [Rat.sub_eq_add_neg]
  · have hbound :
        (ArctanGeometry.arctanIntegralRectangleCompute I.hi
            (arctanScheduledStage n)).hi -
          (ArctanGeometry.arctanIntegralRectangleCompute I.lo
            (arctanScheduledStage n)).lo <=
        (I.hi - I.lo) +
          1 / (((16 * (n + 1) : Nat) : Rat)) * 2 := by
      grind [Rat.sub_eq_add_neg]
    have hsum :
        1 / (((2 * (n + 1) : Nat) : Rat)) +
          1 / (((16 * (n + 1) : Nat) : Rat)) * 2 <=
          1 / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.natCast_mul, Rat.natCast_mul]
      rw [Rat.div_def, Rat.div_def, Rat.div_def]
      have hNne : ((n + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hNpos
      have h2ne : (2 : Rat) ≠ 0 := by native_decide
      have h16ne : (16 : Rat) ≠ 0 := by native_decide
      rw [Rat.inv_mul_rev, Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel _ hNne,
        Rat.mul_inv_cancel _ h2ne,
        Rat.mul_inv_cancel _ h16ne]
    exact Rat.le_trans hbound (Rat.add_le_add hstep hsum)

def arctanScheduledRectangleOnUnit_intervalRegular :
    IntervalRegularOn arctanScheduledRectangleOnUnit where
  evalInterval := fun I hI n =>
    let hLo : inDomainInterval 0 1 I.lo :=
      ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
    let hHi : inDomainInterval 0 1 I.hi :=
      ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
    { lo := (arctanScheduledRectangleOnUnit.compute I.lo hLo n).lo
      hi := (arctanScheduledRectangleOnUnit.compute I.hi hHi n).hi }
  inputPrecision := fun n => 2 * (n + 1)
  inputPrecision_pos := by
    intro n
    omega
  output_width := by
    intro I hI n hsmall
    change 0 <= I.lo ∧ I.lo <= I.hi ∧ I.hi <= 1 at hI
    let hLo : inDomainInterval 0 1 I.lo :=
      ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
    let hHi : inDomainInterval 0 1 I.hi :=
      ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
    by_cases hzero : I.lo = I.hi
    · have hbox := arctanScheduledRectangleOnUnit_width_le I.lo hLo.1 hLo.2 n
      change 0 <= _ ∧ _ <= 1 / (((n + 1 : Nat) : Rat))
      constructor
      · exact (arctanScheduledRectangleOnUnit.valid_on I.lo hLo).1 n
          |> fun h => h
      · rw [← hzero]
        exact Rat.le_trans hbox (by
          rw [Rat.div_def]
          have hNpos : 0 < ((n + 1 : Nat) : Rat) :=
            (Rat.natCast_pos).2 (Nat.succ_pos n)
          exact Rat.mul_le_mul_of_nonneg_right
            (by native_decide : (1 : Rat) / 16 <= 1)
            (Rat.le_of_lt hNpos))
    · exact arctanScheduledRectangleOnUnit_endpointImage_width_le I ⟨hI.1, hI.2.1, hI.2.2⟩ n
        hLo hHi hsmall (by grind [hzero, Rat.sub_eq_add_neg])
  contains_point_values := by
    intro I hI x hx n hIlo hIhi
    change 0 <= I.lo ∧ I.lo <= I.hi ∧ I.hi <= 1 at hI
    let hLo : inDomainInterval 0 1 I.lo :=
      ⟨hI.1, Rat.le_trans hI.2.1 hI.2.2⟩
    let hHi : inDomainInterval 0 1 I.hi :=
      ⟨Rat.le_trans hI.1 hI.2.1, hI.2.2⟩
    change
      (arctanScheduledRectangleOnUnit.compute I.lo hLo n).lo <=
          (arctanScheduledRectangleOnUnit.compute x hx n).lo ∧
        (arctanScheduledRectangleOnUnit.compute x hx n).hi <=
          (arctanScheduledRectangleOnUnit.compute I.hi hHi n).hi
    constructor
    · exact ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
        hI.1 hIlo n
    · exact ArctanGeometry.arctanIntegralRectangleCompute_lower_le_upper_of_le
        (by exact Rat.le_trans hIlo hIhi) hI.2.2 n

/-- The scheduled rectangle branch now has all data required by the inverse
search interface: interval regularity, weak monotonicity, and strict finite
separation. -/
def arctanScheduledRectangleOnUnit_invertible :
    InvertibleFunctionOnInterval where
  continuous :=
    { function := arctanScheduledRectangleOnUnit
      regular := arctanScheduledRectangleOnUnit_intervalRegular }
  source_ordered := by native_decide
  monotone := arctanScheduledRectangleOnUnit_monotone
  separation := arctanScheduledRectangleOnUnit_effectiveInverseSeparation
  orientation := trivial

end ComputableAnalysis
