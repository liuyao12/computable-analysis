import ComputableAnalysis.ModularForms.CMGrowthSharperBounds163

/-! A checked geometric-angle enclosure improves the actual CM exponent upper bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- A finite geometric-angle box supplies a represented upper bound independent of stage choices. -/
theorem halfPi_upper_fifteen_eighths : GeometricPiRotation.halfPi.Le (RealRaw.ofRat (15/8)) := by
  intro n m
  have hbox : (GeometricPiRotation.halfPiUnscheduled.compute 4).hi≤(15/8:Rat) := by decide +kernel
  have h := RealRaw.le_refl GeometricPiRotation.halfPiUnscheduled
    GeometricPiRotation.halfPiUnscheduled_valid (GeometricPiRotation.halfPiStageSchedule.stage n) 4
  change (GeometricPiRotation.halfPiUnscheduled.compute (GeometricPiRotation.halfPiStageSchedule.stage n)).lo≤15/8
  exact Rat.le_trans h hbox

/-- The actual CM growth exponent is bounded above by forty-nine. -/
theorem cmGrowthReal163_upper_fortyNine : cmGrowthReal163.Le (RealRaw.ofRat 49) := by
  intro n m
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid n
  have hr := RealRaw.interval_order_of_valid _ sqrt163_valid n
  have hl := sqrt163_upper_thirteen n 0
  change (sqrt163.compute n).lo≤(13:Rat) at hl
  have hp := QBox.mulRealInterval_contains (Rat.le_refl) ho (Rat.le_refl) hr
  have h1 := halfPi_upper_fifteen_eighths n 0
  change (GeometricPiRotation.halfPi.compute n).lo≤(15/8:Rat) at h1
  have hn : 0≤(sqrt163.compute n).lo := (sqrtRaw_stage_spec 163 (by unfold sqrtDomain; decide +kernel) n).1
  have hm := Rat.mul_le_mul_of_nonneg_right h1 hn
  have ht := Rat.mul_le_mul_of_nonneg_left hl (show (0:Rat)≤15/8 by decide +kernel)
  have hb : (QBox.mulRealInterval (GeometricPiRotation.halfPi.compute n).lo
      (GeometricPiRotation.halfPi.compute n).hi (sqrt163.compute n).lo (sqrt163.compute n).hi).lo≤195/8 := by
    grind only
  have hs := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤2 by decide +kernel)
  change 2*(QBox.mulRealInterval (GeometricPiRotation.halfPi.compute n).lo
    (GeometricPiRotation.halfPi.compute n).hi (sqrt163.compute n).lo (sqrt163.compute n).hi).lo≤(49:Rat)
  grind only

end ComputableAnalysis.ModularForms
