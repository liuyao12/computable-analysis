import ComputableAnalysis.ModularForms.CMRealExponent163

/-! Explicit represented order bounds for the CM growth exponent. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem rootNonnegative (n : Nat) : 0 ≤ (sqrt163.compute n).lo := by
  have hs := sqrtRaw_stage_spec 163 (by unfold sqrtDomain; decide +kernel) n
  exact hs.1

theorem cmGrowthReal163_lower_twentyFour : (RealRaw.ofRat 24).Le cmGrowthReal163 := by
  intro n m
  have hhalf := GeometricPiRotation.halfPi_bounds m
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid m
  have hr := RealRaw.interval_order_of_valid _ sqrt163_valid m
  have hl := sqrt163_lower_twelve 0 m
  change (12:Rat) ≤ (sqrt163.compute m).hi at hl
  have hp := QBox.mulRealInterval_contains ho (Rat.le_refl) hr (Rat.le_refl)
  have h1 : (1:Rat) ≤ (GeometricPiRotation.halfPi.compute m).hi := Rat.le_trans hhalf.1 ho
  have hn : 0 ≤ (sqrt163.compute m).hi := Rat.le_trans (by decide) hl
  have hm := Rat.mul_le_mul_of_nonneg_right h1 hn
  have ht : (12:Rat) ≤
      (QBox.mulRealInterval (GeometricPiRotation.halfPi.compute m).lo
        (GeometricPiRotation.halfPi.compute m).hi (sqrt163.compute m).lo (sqrt163.compute m).hi).hi := by
    grind only
  have hs := Rat.mul_le_mul_of_nonneg_left ht (show (0:Rat)≤2 by decide)
  change (24:Rat) ≤ 2*
    (QBox.mulRealInterval (GeometricPiRotation.halfPi.compute m).lo
      (GeometricPiRotation.halfPi.compute m).hi (sqrt163.compute m).lo (sqrt163.compute m).hi).hi
  grind only

theorem cmGrowthReal163_upper_fiftyTwo : cmGrowthReal163.Le (RealRaw.ofRat 52) := by
  intro n m
  have hhalf := GeometricPiRotation.halfPi_bounds n
  have ho := RealRaw.interval_order_of_valid _ GeometricPiRotation.halfPi_valid n
  have hr := RealRaw.interval_order_of_valid _ sqrt163_valid n
  have hl := sqrt163_upper_thirteen n 0
  change (sqrt163.compute n).lo ≤ (13:Rat) at hl
  have hp := QBox.mulRealInterval_contains (Rat.le_refl) ho (Rat.le_refl) hr
  have h1 := Rat.le_trans ho hhalf.2
  have hm := Rat.mul_le_mul_of_nonneg_right h1 (rootNonnegative n)
  have ht := Rat.mul_le_mul_of_nonneg_left hl (show (0:Rat)≤2 by decide)
  have hb : (QBox.mulRealInterval (GeometricPiRotation.halfPi.compute n).lo
      (GeometricPiRotation.halfPi.compute n).hi (sqrt163.compute n).lo (sqrt163.compute n).hi).lo ≤ 26 := by
    grind only
  have hs := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤2 by decide)
  change 2*(QBox.mulRealInterval (GeometricPiRotation.halfPi.compute n).lo
      (GeometricPiRotation.halfPi.compute n).hi (sqrt163.compute n).lo (sqrt163.compute n).hi).lo ≤ (52:Rat)
  grind only

theorem cmGrowthReal163_positive : cmGrowthReal163.Pos := by
  obtain ⟨N,hN⟩ := cmGrowthReal163_valid.2.2 (⟨1,by decide⟩ : QPos)
  have hw := hN N (Nat.le_refl N)
  have hl := cmGrowthReal163_lower_twentyFour 0 N
  change (24:Rat) ≤ (cmGrowthReal163.compute N).hi at hl
  unfold QInterval.width at hw
  refine ⟨N,?_⟩
  change 0 < (cmGrowthReal163.compute N).lo
  grind only

theorem cmGrowthExponent163_small : Small cmGrowthExponent163.val 52 := by
  have hb : Small (ofRealRaw cmGrowthReal163) 52 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro n m
      have hl := cmGrowthReal163_lower_twentyFour 0 m
      change (24:Rat) ≤ (cmGrowthReal163.compute m).hi at hl
      change (-52:Rat) ≤ (cmGrowthReal163.compute m).hi
      grind only
    · intro n m; exact cmGrowthReal163_upper_fiftyTwo n m
    · intro n m; change (-52:Rat) ≤ 0; decide
    · intro n m; change (0:Rat) ≤ 52; decide
  exact Small.congr (ofRealRaw_valid _ cmGrowthReal163_valid) cmGrowthExponent163.property
    (equiv_symm cmGrowthExponent163_real) hb

def cmExponentialRadius163 : QPos := ⟨53,by decide⟩

theorem cmGrowthExponent163_chart :
    (exponentialChart cmExponentialRadius163).domain cmGrowthExponent163 :=
  ⟨52,by decide,by decide,cmGrowthExponent163_small⟩

end ComputableAnalysis.ModularForms
