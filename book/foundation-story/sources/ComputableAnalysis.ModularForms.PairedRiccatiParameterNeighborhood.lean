import ComputableAnalysis.ModularForms.RepresentedNeighborhoodDisplacement
import ComputableAnalysis.ModularForms.PairedRiccatiUniformLocalVariation

/-! Actual Riccati variation on rational parameter neighborhoods of every
represented affine-segment point. Radii are constructed from derivative data. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem pairedRiccati_parameter_neighborhood (p q : Scalar) (W : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (t : UnitInterval.Point) (eps : QPos) :
    ∃ r : QPos, ∀ u : Rat, 0≤u → u≤1 →
      RealRaw.Le (RealRaw.ofRat (u-r.val)) t.value →
      RealRaw.Le t.value (RealRaw.ofRat (u+r.val)) →
      Small (sub (pairedEntireRiccatiMap.eval (AffineSegment.point p q u) trivial).val
        (pairedEntireRiccatiMap.eval (RepresentedAffineSegment.point p q t) trivial).val)
        eps.val := by
  let a := RepresentedAffineSegment.point p q t
  let D := (pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta unitError
  have hC : (0:Rat)<2854864385 := by decide +kernel
  have hE : 0<eps.val/2854864385 := by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr hC)
  let H : QPos := ⟨min D.val (eps.val/2854864385), by
    have hD := D.property
    change 0<min D.val (eps.val/2854864385)
    grind⟩
  have hden : 0<2*W.val := Rat.mul_pos (by decide +kernel) W.property
  let r : QPos := ⟨H.val/(2*W.val), by
    rw [Rat.div_def]
    exact Rat.mul_pos H.property (Rat.inv_pos.mpr hden)⟩
  refine ⟨r, ?_⟩
  intro u hu0 hu1 hl hh
  have hb := representedAffine_rational_neighborhood p q t u hu0 hu1 W.val r.val
    (Rat.le_of_lt W.property) (Rat.le_of_lt r.property) hd hl hh
  have he : 2*W.val*r.val=H.val := by
    change (2*W.val)*(H.val/(2*W.val))=H.val
    rw [Rat.div_def, Rat.mul_comm H.val, ← Rat.mul_assoc,
      Rat.mul_inv_cancel (2*W.val) (Rat.ne_of_gt hden), Rat.one_mul]
  rw [he] at hb
  have hHD : H.val≤D.val := by dsimp [H]; grind
  have hv := pairedEntireRiccatiMap_uniform_local_variation a
    (AffineSegment.point p q u) H hHD hb
  apply hv.mono
  have hHE : H.val≤eps.val/2854864385 := by dsimp [H]; grind
  have hm := Rat.mul_le_mul_of_nonneg_left hHE (Rat.le_of_lt hC)
  have hc : 2854864385*(eps.val/2854864385)=eps.val := by
    rw [Rat.div_def, Rat.mul_comm eps.val, ← Rat.mul_assoc,
      Rat.mul_inv_cancel 2854864385 (Rat.ne_of_gt hC), Rat.one_mul]
  rw [hc] at hm
  exact hm

end ComputableAnalysis.ModularForms
