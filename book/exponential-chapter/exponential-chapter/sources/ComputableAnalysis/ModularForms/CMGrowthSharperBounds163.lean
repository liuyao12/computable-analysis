import ComputableAnalysis.ModularForms.CMGrowthBounds163

/-! A stronger actual lower bound for the represented CM growth exponent. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- A checked finite geometric-angle box gives a global represented lower bound. -/
theorem halfPi_lower_three_halves : (RealRaw.ofRat (3/2)).Le GeometricPiRotation.halfPi := by
  intro n m
  let s := GeometricPiRotation.halfPiStageSchedule.stage m
  let k := max 4 s
  have h0 : (3/2:Rat)≤(GeometricPiRotation.halfPiUnscheduled.compute 4).lo := by decide +kernel
  have ha := GeometricPiRotation.halfPiUnscheduled_valid.2.1 4 k (Nat.le_max_left _ _)
  have hb := GeometricPiRotation.halfPiUnscheduled_valid.2.1 s k (Nat.le_max_right _ _)
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPiUnscheduled_valid k
  change (3/2:Rat)≤(GeometricPiRotation.halfPiUnscheduled.compute s).hi
  exact Rat.le_trans h0 (Rat.le_trans ha.1 (Rat.le_trans ho hb.2.2))

/-- The actual CM growth exponent is at least thirty-six. -/
theorem cmGrowthReal163_lower_thirtySix : (RealRaw.ofRat 36).Le cmGrowthReal163 := by
  intro n m
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid m
  have hr := RealRaw.interval_order_of_valid _ sqrt163_valid m
  have hl := sqrt163_lower_twelve 0 m
  change (12:Rat)≤(sqrt163.compute m).hi at hl
  have hp := QBox.mulRealInterval_contains ho (Rat.le_refl) hr (Rat.le_refl)
  have h1 := halfPi_lower_three_halves 0 m
  change (3/2:Rat)≤(GeometricPiRotation.halfPi.compute m).hi at h1
  have hn : 0≤(sqrt163.compute m).hi := Rat.le_trans (by decide +kernel) hl
  have hm := Rat.mul_le_mul_of_nonneg_right h1 hn
  have ht : (18:Rat)≤
      (QBox.mulRealInterval (GeometricPiRotation.halfPi.compute m).lo
        (GeometricPiRotation.halfPi.compute m).hi (sqrt163.compute m).lo (sqrt163.compute m).hi).hi := by
    grind only
  have hs := Rat.mul_le_mul_of_nonneg_left ht (show (0:Rat)≤2 by decide +kernel)
  change (36:Rat)≤2*
    (QBox.mulRealInterval (GeometricPiRotation.halfPi.compute m).lo
      (GeometricPiRotation.halfPi.compute m).hi (sqrt163.compute m).lo (sqrt163.compute m).hi).hi
  grind only

end ComputableAnalysis.ModularForms
