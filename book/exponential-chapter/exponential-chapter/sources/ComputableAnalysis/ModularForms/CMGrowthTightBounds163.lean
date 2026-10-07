import ComputableAnalysis.ModularForms.CMGrowthSharperUpperBounds163

/-! A narrow justified represented enclosure for the actual CM growth exponent. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- A checked finite geometric angle box gives the sharper half-pi lower bound. -/
theorem halfPi_lower_onePointFiveSeven : (RealRaw.ofRat (157/100)).Le GeometricPiRotation.halfPi := by
  intro n m
  have hbox : (157/100:Rat)≤(GeometricPiRotation.halfPiUnscheduled.compute 8).lo := by decide +kernel
  have h := RealRaw.le_refl GeometricPiRotation.halfPiUnscheduled
    GeometricPiRotation.halfPiUnscheduled_valid 8 (GeometricPiRotation.halfPiStageSchedule.stage m)
  change (157/100:Rat)≤(GeometricPiRotation.halfPiUnscheduled.compute (GeometricPiRotation.halfPiStageSchedule.stage m)).hi
  exact Rat.le_trans hbox h

/-- A checked finite geometric angle box gives the sharper half-pi upper bound. -/
theorem halfPi_upper_eight_fifths : GeometricPiRotation.halfPi.Le (RealRaw.ofRat (8/5)) := by
  intro n m
  have hbox : (GeometricPiRotation.halfPiUnscheduled.compute 8).hi≤(8/5:Rat) := by decide +kernel
  have h := RealRaw.le_refl GeometricPiRotation.halfPiUnscheduled
    GeometricPiRotation.halfPiUnscheduled_valid (GeometricPiRotation.halfPiStageSchedule.stage n) 8
  change (GeometricPiRotation.halfPiUnscheduled.compute (GeometricPiRotation.halfPiStageSchedule.stage n)).lo≤(8/5:Rat)
  exact Rat.le_trans h hbox

/-- The actual represented square root has the rational lower bound 51/4. -/
theorem sqrt163_lower_fiftyOne_quarters : (RealRaw.ofRat (51/4)).Le sqrt163 := by
  intro n m
  have hs := sqrtRaw_stage_spec 163 (by unfold sqrtDomain; decide +kernel) m
  exact hs.le_hi_of_sq_le (r := 51/4) (by decide +kernel)

/-- The actual represented square root has the rational upper bound 64/5. -/
theorem sqrt163_upper_sixtyFour_fifths : sqrt163.Le (RealRaw.ofRat (64/5)) := by
  intro n m
  have hs := sqrtRaw_stage_spec 163 (by unfold sqrtDomain; decide +kernel) n
  exact hs.lo_le_of_sq_le (r := 64/5) (by decide +kernel) (by decide +kernel)

/-- The actual CM growth exponent has a rational lower bound strictly above forty. -/
theorem cmGrowthReal163_lower_tight : (RealRaw.ofRat (8007/200)).Le cmGrowthReal163 := by
  intro n m
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid m
  have hr := RealRaw.interval_order_of_valid _ sqrt163_valid m
  have hl := sqrt163_lower_fiftyOne_quarters 0 m
  change (51/4:Rat)≤(sqrt163.compute m).hi at hl
  have hp := QBox.mulRealInterval_contains ho (Rat.le_refl) hr (Rat.le_refl)
  have h1 := halfPi_lower_onePointFiveSeven 0 m
  change (157/100:Rat)≤(GeometricPiRotation.halfPi.compute m).hi at h1
  have hn : 0≤(sqrt163.compute m).hi := Rat.le_trans (by decide +kernel) hl
  have hm := Rat.mul_le_mul_of_nonneg_right h1 hn
  have hh := Rat.mul_le_mul_of_nonneg_left hl (show (0:Rat)≤157/100 by decide +kernel)
  have hc : (8007/400:Rat)≤(157/100)*(51/4) := by decide +kernel
  have ht : (8007/400:Rat)≤(QBox.mulRealInterval (GeometricPiRotation.halfPi.compute m).lo
      (GeometricPiRotation.halfPi.compute m).hi (sqrt163.compute m).lo (sqrt163.compute m).hi).hi := by
    have hprod := Rat.le_trans hc (Rat.le_trans hh hm)
    grind only
  have hs := Rat.mul_le_mul_of_nonneg_left ht (show (0:Rat)≤2 by decide +kernel)
  change (8007/200:Rat)≤2*(QBox.mulRealInterval (GeometricPiRotation.halfPi.compute m).lo
    (GeometricPiRotation.halfPi.compute m).hi (sqrt163.compute m).lo (sqrt163.compute m).hi).hi
  have hlast : (8007/200:Rat)=2*(8007/400) := by decide +kernel
  rw [hlast]
  exact hs

/-- The actual CM growth exponent has a rational upper bound strictly below forty-one. -/
theorem cmGrowthReal163_upper_tight : cmGrowthReal163.Le (RealRaw.ofRat (1024/25)) := by
  intro n m
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid n
  have hr := RealRaw.interval_order_of_valid _ sqrt163_valid n
  have hl := sqrt163_upper_sixtyFour_fifths n 0
  change (sqrt163.compute n).lo≤(64/5:Rat) at hl
  have hp := QBox.mulRealInterval_contains (Rat.le_refl) ho (Rat.le_refl) hr
  have h1 := halfPi_upper_eight_fifths n 0
  change (GeometricPiRotation.halfPi.compute n).lo≤(8/5:Rat) at h1
  have hn : 0≤(sqrt163.compute n).lo := (sqrtRaw_stage_spec 163 (by unfold sqrtDomain; decide +kernel) n).1
  have hm := Rat.mul_le_mul_of_nonneg_right h1 hn
  have ht := Rat.mul_le_mul_of_nonneg_left hl (show (0:Rat)≤8/5 by decide +kernel)
  have hc : (8/5:Rat)*(64/5)=512/25 := by decide +kernel
  have hb : (QBox.mulRealInterval (GeometricPiRotation.halfPi.compute n).lo
      (GeometricPiRotation.halfPi.compute n).hi (sqrt163.compute n).lo (sqrt163.compute n).hi).lo≤512/25 := by
    have hprod := Rat.le_trans hm ht
    rw [hc] at hprod
    grind only
  have hs := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤2 by decide +kernel)
  have hlast : (2:Rat)*(512/25)≤1024/25 := by decide +kernel
  change 2*(QBox.mulRealInterval (GeometricPiRotation.halfPi.compute n).lo
    (GeometricPiRotation.halfPi.compute n).hi (sqrt163.compute n).lo (sqrt163.compute n).hi).lo≤(1024/25:Rat)
  exact Rat.le_trans hs hlast

/-- The actual CM growth exponent is at least forty. -/
theorem cmGrowthReal163_lower_forty : (RealRaw.ofRat 40).Le cmGrowthReal163 := by
  intro n m
  have h := cmGrowthReal163_lower_tight 0 m
  change (8007/200:Rat)≤(cmGrowthReal163.compute m).hi at h
  exact Rat.le_trans (show (40:Rat)≤8007/200 by decide +kernel) h

/-- The actual CM growth exponent is at most forty-one. -/
theorem cmGrowthReal163_upper_fortyOne : cmGrowthReal163.Le (RealRaw.ofRat 41) := by
  intro n m
  have h := cmGrowthReal163_upper_tight n 0
  change (cmGrowthReal163.compute n).lo≤(1024/25:Rat) at h
  exact Rat.le_trans h (show (1024/25:Rat)≤41 by decide +kernel)


end ComputableAnalysis.ModularForms
