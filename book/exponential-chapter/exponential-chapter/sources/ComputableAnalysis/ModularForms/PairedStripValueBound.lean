import ComputableAnalysis.ModularForms.PairedHeightBalancedCutoff
import ComputableAnalysis.ModularForms.PairedExactUpperStripDerivativeBound

/-! Uniform actual value bounds from a height-balanced rational-box cutoff. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedPartialFractionMap_upper_strip_box_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat)
    (him : 1≤(z.val.compute N).lo.im)
    (hre : -3≤(z.val.compute N).lo.re) (hhi : (z.val.compute N).hi.re≤3)
    (hh : (z.val.compute N).height≤1) :
    Small (pairedPartialFractionMap.eval z hz).val 400 := by
  let eta := (z.val.compute N).lo.im
  let B := pairedHeightBalancedCutoff z N
  have hb := pairedHeightBalancedCutoff_bounds z N him hre hhi hh
  have he : 0<eta := by dsimp [eta]; grind only
  have hs := pairedPartialFractionMap_vertical_bound_at_cutoff z hz N eta he
    (Rat.le_refl) B hb.2.1 hb.1
  have hi : 0≤eta⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr he)
  have hc := Rat.mul_inv_cancel eta (Rat.ne_of_gt he)
  have h1 := Rat.mul_le_mul_of_nonneg_right him hi
  have h2 := Rat.mul_le_mul_of_nonneg_right hb.2.2 hi
  apply hs.mono
  simp only [Rat.div_def,Rat.natCast_mul,show ((4:Nat):Rat)=4 by decide +kernel]
  change 8*eta⁻¹+(4*(B:Rat))*(16*eta⁻¹)+4≤400
  change 1*eta⁻¹≤eta*eta⁻¹ at h1
  change (B:Rat)*eta⁻¹≤(6*eta)*eta⁻¹ at h2
  grind only

theorem exactUpperStrip_has_height_balanced_box (z : Scalar)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    ∃ N, -3≤(z.val.compute N).lo.re ∧ (z.val.compute N).hi.re≤3 ∧
      1≤(z.val.compute N).lo.im ∧ (z.val.compute N).height≤1 := by
  obtain ⟨N,hN⟩ := z.property.2.2 ⟨1,by decide +kernel⟩
  have hw := (hN N (Nat.le_refl N)).1
  have hh := (hN N (Nat.le_refl N)).2
  have hlo := hre 0 N
  have hup := hhi N 0
  have himag := him 0 N
  change 0≤(z.val.compute N).hi.re at hlo
  change (z.val.compute N).lo.re≤2 at hup
  change 2≤(z.val.compute N).hi.im at himag
  change (z.val.compute N).hi.re-(z.val.compute N).lo.re≤1 at hw
  have hheight := hh
  change (z.val.compute N).hi.im-(z.val.compute N).lo.im≤1 at hh
  exact ⟨N,by grind only,by grind only,by grind only,hheight⟩

theorem pairedPartialFractionMap_exact_upper_strip_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val)
    (hre : RealRaw.Le (RealRaw.ofRat 0) z.val.realPart)
    (hhi : RealRaw.Le z.val.realPart (RealRaw.ofRat 2))
    (him : RealRaw.Le (RealRaw.ofRat 2) z.val.imagPart) :
    Small (pairedPartialFractionMap.eval z hz).val 400 := by
  obtain ⟨N,hlo,hup,hheight,hh⟩ := exactUpperStrip_has_height_balanced_box z hre hhi him
  exact pairedPartialFractionMap_upper_strip_box_bound z hz N hheight hlo hup hh

end ComputableAnalysis.ModularForms
