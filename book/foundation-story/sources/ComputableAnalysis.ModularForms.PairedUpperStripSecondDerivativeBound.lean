import ComputableAnalysis.ModularForms.PairedHeightBalancedSecondDerivativeRoom

/-! Uniform canonical second-derivative control on certified upper-strip boxes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedCanonicalSecondDerivative_upper_strip_box_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat)
    (him : 1≤(z.val.compute N).lo.im)
    (hre : -3≤(z.val.compute N).lo.re) (hhi : (z.val.compute N).hi.re≤3)
    (hh : (z.val.compute N).height≤1) :
    Small (pairedCanonicalSecondDerivative z hz).val 364544 := by
  let eta := (z.val.compute N).lo.im
  let B := pairedHeightBalancedSecondDerivativeCutoff z N
  have hb := pairedHeightBalancedSecondDerivativeCutoff_bounds z N him hre hhi hh
  have hr := pairedHeightBalancedCutoff_second_derivative_room z N him hre hhi
  have he : 0<eta := by dsimp [eta]; grind only
  have hs := pairedCanonicalSecondDerivative_vertical_regional_bound z hz B hr N eta he (Rat.le_refl)
  have hi : 0≤eta⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr he)
  have hc := Rat.mul_inv_cancel eta (Rat.ne_of_gt he)
  have h1 := Rat.mul_le_mul_of_nonneg_right him hi
  have h2 := Rat.mul_le_mul_of_nonneg_right hb.2 hi
  have hi1 : eta⁻¹≤1 := by change 1*eta⁻¹≤eta*eta⁻¹ at h1; grind only
  have hb1 : (B:Rat)*eta⁻¹≤7 := by grind only
  have hi2 : eta⁻¹*eta⁻¹≤1 := by
    have h := Rat.mul_le_mul_of_nonneg_right hi1 hi
    grind only
  have hi3 : eta⁻¹*eta⁻¹*eta⁻¹≤1 := by
    have h := Rat.mul_le_mul_of_nonneg_right hi2 hi
    grind only
  have hb2 : (B:Rat)*eta⁻¹*eta⁻¹≤7 := by
    have h := Rat.mul_le_mul_of_nonneg_right hb1 hi
    have h' := Rat.mul_le_mul_of_nonneg_left hi1 (show (0:Rat)≤7 by decide +kernel)
    grind only
  have hb3 : (B:Rat)*eta⁻¹*eta⁻¹*eta⁻¹≤7 := by
    have h := Rat.mul_le_mul_of_nonneg_right hb2 hi
    have h' := Rat.mul_le_mul_of_nonneg_left hi1 (show (0:Rat)≤7 by decide +kernel)
    grind only
  apply hs.mono
  simp only [Rat.div_def,Rat.natCast_mul,show ((4:Nat):Rat)=4 by decide +kernel]
  have hA := Rat.mul_le_mul_of_nonneg_left hi3 (show (0:Rat)≤4096 by decide +kernel)
  have hB := Rat.mul_le_mul_of_nonneg_left hb3 (show (0:Rat)≤32768 by decide +kernel)
  grind only

theorem pairedCanonicalSecondDerivative_exact_upper_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedCanonicalSecondDerivative z hz).val 364544 := by
  obtain ⟨N,hr,hh,hi,hheight⟩ := exactUpperStrip_has_height_balanced_box z hre hhi him
  exact pairedCanonicalSecondDerivative_upper_strip_box_bound z hz N hi hr hh hheight

end ComputableAnalysis.ModularForms
