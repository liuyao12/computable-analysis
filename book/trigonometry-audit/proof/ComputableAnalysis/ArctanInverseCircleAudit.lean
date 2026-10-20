import ComputableAnalysis.ArctanInverseCircle

/-! Exact identification checks for the concrete geometric-arctangent inverse.
The target is an angle divided by two. Circle coordinates are checked against
every rational slope in the unit chart, not against decimal samples. -/
namespace ComputableAnalysis.ArctanInverseCircleAudit
open ArctanSecantFoundation ArctanInverseConstruction ArctanInverseCircle
open SinPiIntegral
set_option maxHeartbeats 2000000

theorem value_order_reflects {a b : Rat}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (h : (value a).Le (value b)) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have hgap : 0 < a-b := by grind
    let n := (a-b).den
    have hsmall := one_div_den_succ_le_of_pos hgap
    have hsep : b + 1 / (((n+1:Nat):Rat)) ≤ a := by
      dsimp [n]
      grind only
    have hs := arctanScheduledRectangleOnUnit_strict_separation
      hb.1 hb.2 ha.1 ha.2 n hsep
    have hc := h n n
    change ((arctanScheduledRectangleRaw a).compute n).lo ≤
      ((arctanScheduledRectangleRaw b).compute n).hi at hc
    grind only

theorem value_order {a b : Rat}
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hab : a ≤ b) :
    (value a).Le (value b) := by
  apply RealRaw.le_of_sameStage (value_valid ha) (value_valid hb)
  intro n
  have h := (increment_bounds ha.1 hab n).1
  have hk : 0 ≤ ArctanGeometry.integralKernel b :=
    Rat.le_trans (by decide +kernel : (0:Rat)≤1/2) (kernel_bounds hb).1
  have hm := Rat.mul_nonneg (show 0≤b-a by grind only) hk
  grind only

theorem inverse_contains_preimage (Y : RealRaw) (hy : Y.Valid)
    (ht : ∀ n, (Y.compute (precision n)).width ≤ width n/128)
    (hrange : (value 0).Le Y ∧ Y.Le (value 1))
    (u : Rat) (hu : 0 ≤ u ∧ u ≤ 1) (hangle : Y.Equiv (value u))
    (n : Nat) :
    ((inverseExtension Y).compute n).lo ≤ u ∧
      u ≤ ((inverseExtension Y).compute n).hi := by
  have hb := bracket_target Y hy ht hrange n
  have hg := bracket_geometry Y n
  have hYu := RealRaw.le_of_equiv hy (value_valid hu) hangle
  have huY := RealRaw.le_of_equiv (value_valid hu) hy (RealRaw.equiv_symm hangle)
  exact ⟨value_order_reflects ⟨hg.1, Rat.le_trans hg.2.1 hg.2.2.1⟩ hu
      (RealRaw.le_trans hy hb.1 hYu),
    value_order_reflects hu ⟨Rat.le_trans hg.1 hg.2.1,hg.2.2.1⟩
      (RealRaw.le_trans hy huY hb.2)⟩

theorem inverse_at_geometric_source (u : Rat) (hu : 0 ≤ u ∧ u ≤ 1) :
    (inverseExtension (value u)).Equiv (RealRaw.ofRat u) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  exact inverse_contains_preimage (value u) (value_valid hu)
    (source_width u hu) ⟨value_order ⟨by decide +kernel,by decide +kernel⟩ hu hu.1,
      value_order hu ⟨by decide +kernel,by decide +kernel⟩ hu.2⟩
    u hu (RealRaw.equiv_refl _ (value_valid hu)) n

def sineAtHalfAngle (Y : RealRaw) : RealRaw where
  compute n := rationalCircleSinInterval ((inverseExtension Y).compute n)

def cosineAtHalfAngle (Y : RealRaw) : RealRaw where
  compute n := rationalCircleCosInterval ((inverseExtension Y).compute n)

theorem sineAtHalfAngle_valid (Y : RealRaw) : (sineAtHalfAngle Y).Valid :=
  rationalCircleSinInterval_valid _ (inverseExtension_valid _) (fun n =>
    ⟨(bracket_geometry _ n).1,(bracket_geometry _ n).2.2.1⟩)

theorem cosineAtHalfAngle_valid (Y : RealRaw) : (cosineAtHalfAngle Y).Valid :=
  rationalCircleCosInterval_valid _ (inverseExtension_valid _) (fun n =>
    ⟨(bracket_geometry _ n).1,(bracket_geometry _ n).2.2.1⟩)

theorem circle_coordinates_at_preimage (Y : RealRaw) (hy : Y.Valid)
    (ht : ∀ n, (Y.compute (precision n)).width ≤ width n/128)
    (hrange : (value 0).Le Y ∧ Y.Le (value 1))
    (u : Rat) (hu : 0 ≤ u ∧ u ≤ 1) (hangle : Y.Equiv (value u)) :
    (sineAtHalfAngle Y).Equiv (RealRaw.ofRat (rationalCircleSin u)) ∧
    (cosineAtHalfAngle Y).Equiv (RealRaw.ofRat (rationalCircleCos u)) := by
  have hcontains := inverse_contains_preimage Y hy ht hrange u hu hangle
  constructor
  · intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    have hg := bracket_geometry Y n
    have h := rationalCircleSinInterval_overlap_of_common_point
      (U := (inverseExtension Y).compute n) (V := ⟨u,u⟩)
      ⟨hg.1,hg.2.1,hg.2.2.1⟩ ⟨hu.1,Rat.le_refl,hu.2⟩ u
      (hcontains n) ⟨Rat.le_refl,Rat.le_refl⟩
    exact h
  · intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    have hg := bracket_geometry Y n
    -- Use the closed cosine difference bound at the actual enclosing endpoints.
    have hlo : rationalCircleCos ((bracket Y n).hi) ≤ rationalCircleCos u := by
      have hm := (rationalCircleCosInterval_width_le
        (U := ⟨u,(bracket Y n).hi⟩)
        ⟨hu.1,(hcontains n).2,hg.2.2.1⟩).1
      change 0 ≤ rationalCircleCos u - rationalCircleCos (bracket Y n).hi at hm
      grind only
    have hhi : rationalCircleCos u ≤ rationalCircleCos ((bracket Y n).lo) := by
      have hm := (rationalCircleCosInterval_width_le
        (U := ⟨(bracket Y n).lo,u⟩)
        ⟨hg.1,(hcontains n).1,hu.2⟩).1
      change 0 ≤ rationalCircleCos (bracket Y n).lo-rationalCircleCos u at hm
      grind only
    exact ⟨hlo,hhi⟩

theorem geometric_chart_check (u : Rat) (hu : 0 ≤ u ∧ u ≤ 1) :
    (sineAtHalfAngle (value u)).Equiv (RealRaw.ofRat (rationalCircleSin u)) ∧
    (cosineAtHalfAngle (value u)).Equiv (RealRaw.ofRat (rationalCircleCos u)) :=
  circle_coordinates_at_preimage _ (value_valid hu) (source_width u hu)
    ⟨value_order ⟨by decide +kernel,by decide +kernel⟩ hu hu.1,
      value_order hu ⟨by decide +kernel,by decide +kernel⟩ hu.2⟩
    u hu (RealRaw.equiv_refl _ (value_valid hu))

theorem quarter_chart_check (t u : Rat) (ht : 0 ≤ t ∧ t ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ 1)
    (hangle : (quarterTarget t).Equiv (value u)) :
    (sineQuarter t).Equiv (RealRaw.ofRat (rationalCircleSin u)) ∧
    (cosineQuarter t).Equiv (RealRaw.ofRat (rationalCircleCos u)) :=
  circle_coordinates_at_preimage _ (quarterTarget_valid t)
    (quarterTarget_width t ht) (quarterTarget_range t ht) u hu hangle

private theorem square_mono {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    a*a ≤ b*b :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hab ha)
    (Rat.mul_le_mul_of_nonneg_right hab (Rat.le_trans ha hab))

private theorem rational_coordinate_bounds (u : Rat) (hu : 0 ≤ u ∧ u ≤ 1) :
    0 ≤ rationalCircleSin u ∧ rationalCircleSin u ≤ 1 ∧
      0 ≤ rationalCircleCos u ∧ rationalCircleCos u ≤ 1 := by
  have hsq := Rat.mul_nonneg hu.1 hu.1
  have hsq1 := square_mono hu.1 hu.2
  have hp : 0 < 1+u*u := by grind only
  have hi := Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hdiff := Rat.mul_nonneg (show 0≤1-u by grind only) (show 0≤1-u by grind only)
  have hs0 : 0 ≤ rationalCircleSin u := by
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hu.1) hi
  have hc0 : 0 ≤ rationalCircleCos u := by
    exact Rat.mul_nonneg (show 0≤1-u*u by grind only) hi
  refine ⟨hs0,?_,hc0,?_⟩
  all_goals
    apply Rat.le_of_mul_le_mul_right (c:=1+u*u) _ hp
    simp only [rationalCircleSin,rationalCircleCos]
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hp)]
    grind only [Rat.sub_eq_add_neg,Rat.mul_add,Rat.add_mul,Rat.mul_assoc,Rat.mul_comm]

theorem coordinate_ranges (Y : RealRaw) (n : Nat) :
    0 ≤ ((sineAtHalfAngle Y).compute n).lo ∧
      ((sineAtHalfAngle Y).compute n).hi ≤ 1 ∧
      0 ≤ ((cosineAtHalfAngle Y).compute n).lo ∧
      ((cosineAtHalfAngle Y).compute n).hi ≤ 1 := by
  have hg := bracket_geometry Y n
  have hL := rational_coordinate_bounds (bracket Y n).lo ⟨hg.1,Rat.le_trans hg.2.1 hg.2.2.1⟩
  have hU := rational_coordinate_bounds (bracket Y n).hi ⟨Rat.le_trans hg.1 hg.2.1,hg.2.2.1⟩
  exact ⟨hL.1,hU.2.1,hU.2.2.1,hL.2.2.2⟩

theorem unit_circle (Y : RealRaw) :
    (sineAtHalfAngle Y * sineAtHalfAngle Y +
      cosineAtHalfAngle Y * cosineAtHalfAngle Y).Equiv (RealRaw.ofRat 1) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hr := coordinate_ranges Y n
  have hsorder := RealRaw.interval_order_of_valid _ (sineAtHalfAngle_valid Y) n
  have hcorder := RealRaw.interval_order_of_valid _ (cosineAtHalfAngle_valid Y) n
  have hSsquare := square_mono hr.1 hsorder
  have hCsquare := square_mono hr.2.2.1 hcorder
  change QInterval.Overlaps
    (QInterval.addInterval
      (QBox.mulRealInterval
        ((sineAtHalfAngle Y).compute n).lo ((sineAtHalfAngle Y).compute n).hi
        ((sineAtHalfAngle Y).compute n).lo ((sineAtHalfAngle Y).compute n).hi)
      (QBox.mulRealInterval
        ((cosineAtHalfAngle Y).compute n).lo ((cosineAtHalfAngle Y).compute n).hi
        ((cosineAtHalfAngle Y).compute n).lo ((cosineAtHalfAngle Y).compute n).hi))
    {lo:=1,hi:=1}
  rw [QBox.mulRealInterval_self_of_nonneg hr.1 hsorder,
    QBox.mulRealInterval_self_of_nonneg hr.2.2.1 hcorder]
  have hpoint := rationalCircleSin_sq_add_cos_sq ((bracket Y n).lo)
  change ((sineAtHalfAngle Y).compute n).lo * ((sineAtHalfAngle Y).compute n).lo +
        ((cosineAtHalfAngle Y).compute n).hi * ((cosineAtHalfAngle Y).compute n).hi = 1 at hpoint
  change _ ≤ _ ∧ _ ≤ _
  dsimp only [QInterval.addInterval]
  constructor <;> grind only

theorem quarter_unit_circle (t : Rat) :
    (sineQuarter t * sineQuarter t + cosineQuarter t * cosineQuarter t).Equiv
      (RealRaw.ofRat 1) := unit_circle (quarterTarget t)

private theorem quarter_zero_angle : (quarterTarget 0).Equiv (value 0) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps (QInterval.scaleRat 0 ((value 1).compute n))
    (ArctanGeometry.arctanIntegralRectangleCompute 0 (arctanScheduledStage n))
  have hl := ArctanGeometry.arctanIntegralRectangleCompute_zero_lower (arctanScheduledStage n)
  have hbound := ArctanGeometry.arctanIntegralRectangleCompute_upper_le_input
    (x:=0) (by decide +kernel) (arctanScheduledStage n)
  have horder := ArctanGeometry.arctanIntegralRectangleCompute_ordered
    (x:=0) (by decide +kernel) (arctanScheduledStage n)
  have hh : (ArctanGeometry.arctanIntegralRectangleCompute 0 (arctanScheduledStage n)).hi=0 := by
    unfold QInterval.width at horder
    grind only
  simp only [QInterval.scaleRat, if_pos (show (0:Rat)≤0 from Rat.le_refl),
    Rat.zero_mul, QInterval.Overlaps, hl, hh]
  exact ⟨Rat.le_refl,Rat.le_refl⟩

private theorem quarter_one_angle : (quarterTarget 1).Equiv (value 1) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have ho := RealRaw.interval_order_of_valid _ (value_valid (x:=1) ⟨by decide +kernel,by decide +kernel⟩) n
  change QInterval.Overlaps (QInterval.scaleRat 1 ((value 1).compute n)) ((value 1).compute n)
  simpa only [QInterval.scaleRat,if_pos (show (0:Rat)≤1 from by decide +kernel),
    Rat.one_mul,QInterval.Overlaps] using And.intro ho ho

theorem quarter_endpoints :
    (sineQuarter 0).Equiv (RealRaw.ofRat 0) ∧
    (cosineQuarter 0).Equiv (RealRaw.ofRat 1) ∧
    (sineQuarter 1).Equiv (RealRaw.ofRat 1) ∧
    (cosineQuarter 1).Equiv (RealRaw.ofRat 0) := by
  have h0 := quarter_chart_check 0 0 ⟨by decide +kernel,by decide +kernel⟩
    ⟨by decide +kernel,by decide +kernel⟩ quarter_zero_angle
  have h1 := quarter_chart_check 1 1 ⟨by decide +kernel,by decide +kernel⟩
    ⟨by decide +kernel,by decide +kernel⟩ quarter_one_angle
  have s0 : rationalCircleSin 0=0 := by decide +kernel
  have c0 : rationalCircleCos 0=1 := by decide +kernel
  have s1 : rationalCircleSin 1=1 := by decide +kernel
  have c1 : rationalCircleCos 1=0 := by decide +kernel
  rw [s0,c0] at h0
  rw [s1,c1] at h1
  exact ⟨h0.1,h0.2,h1.1,h1.2⟩

private theorem area_pi_valid : piCircleArea.Valid := by
  have heq : ((4:Nat)*ArctanGeometry.arctanGeom 1 : RealRaw).compute = piCircleArea.compute :=
    funext ArctanGeometry.four_arctanGeom_one_compute_eq_piCircleArea_compute
  change RealRaw.ValidCompute piCircleArea.compute
  rw [←heq]
  exact ArctanGeometry.four_arctanGeom_one_valid

theorem geometric_pi_clock :
    (RealRaw.scaleRat 4 (value 1)).Equiv piCircleArea := by
  have hraw : (ArctanGeometry.arctanIntegralRectangleRaw 1).Equiv
      (ArctanGeometry.arctanGeom 1) := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    change QInterval.Overlaps
      (ArctanGeometry.integralSumInterval (ArctanGeometry.arctanAreaLoopState 1 n).intervals)
      ((ArctanGeometry.arctanGeom 1).compute n)
    rw [ArctanGeometry.arctanGeom_nonneg_compute_eq
      (by decide +kernel : (1:Rat)≠0) (by decide +kernel : (0:Rat)≤1)]
    exact ArctanGeometry.arctanAreaLoop_integralSum_overlaps_positiveLoop (by decide +kernel) n
  have h := RealRaw.equiv_trans
    (value_valid (x:=1) ⟨by decide +kernel,by decide +kernel⟩)
    (ArctanGeometry.arctanIntegralRectangleRaw_valid (x:=1) (by decide +kernel) (by decide +kernel))
    ArctanGeometry.arctanGeom_one_valid
    (RealRaw.equiv_symm (RealRaw.schedule_equiv
      (ArctanGeometry.arctanIntegralRectangleRaw 1)
      (ArctanGeometry.arctanIntegralRectangleRaw_valid (x:=1) (by decide +kernel) (by decide +kernel))
      arctanScheduledStageSchedule)) hraw
  have hscaled := RealRaw.scaleRat_equiv_of_nonneg (r:=4)
    (by decide +kernel) h
  exact RealRaw.equiv_trans
    (RealRaw.scaleRat_valid (value_valid (x:=1) ⟨by decide +kernel,by decide +kernel⟩))
    ArctanGeometry.four_arctanGeom_one_valid area_pi_valid hscaled
    ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea

/-- The inverse target is half the physical angle, so multiplying this
target by four gives pi times the normalized quarter-turn coordinate. -/
theorem quarter_angle_normalization (t : Rat) (ht : 0 ≤ t ∧ t ≤ 1) :
    (RealRaw.scaleRat 4 (quarterTarget t)).Equiv (RealRaw.scaleRat t piCircleArea) := by
  have hv := value_valid (x:=1) ⟨by decide +kernel,by decide +kernel⟩
  have hleft := RealRaw.scaleRat_scaleRat_equiv_of_nonneg 4 t (by decide +kernel) ht.1 (value 1) hv
  have hright := RealRaw.scaleRat_scaleRat_equiv_of_nonneg t 4 ht.1 (by decide +kernel) (value 1) hv
  rw [Rat.mul_comm t 4] at hright
  have hcompare := RealRaw.equiv_trans
    (RealRaw.scaleRat_valid (RealRaw.scaleRat_valid hv))
    (RealRaw.scaleRat_valid hv)
    (RealRaw.scaleRat_valid (RealRaw.scaleRat_valid hv)) hleft (RealRaw.equiv_symm hright)
  exact RealRaw.equiv_trans
    (RealRaw.scaleRat_valid (quarterTarget_valid t))
    (RealRaw.scaleRat_valid (RealRaw.scaleRat_valid hv))
    (RealRaw.scaleRat_valid area_pi_valid) hcompare (RealRaw.scaleRat_equiv geometric_pi_clock)

end ComputableAnalysis.ArctanInverseCircleAudit
