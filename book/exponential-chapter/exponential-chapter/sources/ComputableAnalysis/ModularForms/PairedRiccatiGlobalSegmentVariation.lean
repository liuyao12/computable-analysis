import ComputableAnalysis.ModularForms.PairedRiccatiLocalEndpointVariation
import ComputableAnalysis.ModularForms.RepresentedNeighborhoodDisplacement
import ComputableAnalysis.ModularForms.PairedRiccatiFiniteChainVariation

/-! Whole-segment variation derived by explicit rational bisection.
No uniform mesh-radius hypothesis or segment integral is assumed. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def riccatiEndpointGood (p q : Scalar) (W : Rat) (I : QInterval) : Prop :=
  Small (sub (pairedEntireRiccatiMap.eval (AffineSegment.point p q I.hi) trivial).val
    (pairedEntireRiccatiMap.eval (AffineSegment.point p q I.lo) trivial).val)
    (2854864386*W*I.width)

theorem riccatiEndpointGood_join (p q : Scalar) (W : Rat) (I : QInterval)
    (hl : riccatiEndpointGood p q W (bisectInterval I false))
    (hr : riccatiEndpointGood p q W (bisectInterval I true)) : riccatiEndpointGood p q W I := by
  have hb := LocalODE.small_add hr hl
  let A := pairedEntireRiccatiMap.eval (AffineSegment.point p q I.hi) trivial
  let B := pairedEntireRiccatiMap.eval (AffineSegment.point p q I.midpoint) trivial
  let C := pairedEntireRiccatiMap.eval (AffineSegment.point p q I.lo) trivial
  have hs := Small.congr
    (add_valid (sub_valid A.property B.property) (sub_valid B.property C.property))
    (sub_valid A.property C.property) (representedDifference_split A B C) hb
  have he : 2854864386*W*(bisectInterval I true).width+
      2854864386*W*(bisectInterval I false).width=2854864386*W*I.width := by
    rw [bisectInterval_width,bisectInterval_width]
    grind only
  rw [he] at hs
  exact hs

theorem pairedRiccati_affine_segment_variation (p q : Scalar) (W : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val) :
    Small (sub (pairedEntireRiccatiMap.eval q trivial).val
      (pairedEntireRiccatiMap.eval p trivial).val) (2854864386*W.val) := by
  have good : riccatiEndpointGood p q W.val ⟨0,1⟩ := by
    apply bisection_cover_principle (riccatiEndpointGood p q W.val) ⟨0,1⟩
      (riccatiEndpointGood_join p q W.val)
    intro choice
    have hx := bisectionReal_enclosed (⟨0,1⟩ : QInterval) (by decide +kernel) choice 0
    let t : UnitInterval.Point := ⟨bisectionReal ⟨0,1⟩ choice,
      bisectionReal_valid ⟨0,1⟩ (by decide +kernel) choice,hx.1,hx.2⟩
    let a := RepresentedAffineSegment.point p q t
    let D := (pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta halfDerivativeError
    let N := RationalMajorant.natRateStage (2*W.val) D
    let J := bisectionInterval ⟨0,1⟩ choice N
    have hw : J.width=((1:Rat)/2)^N := by
      have h := bisectionInterval_width (⟨0,1⟩ : QInterval) choice N
      simpa only [QInterval.width,show (1:Rat)-0=1 by decide +kernel,Rat.one_mul] using h
    have hwpos : 0<J.width := by
      rw [hw]
      exact Rat.pow_pos (by decide +kernel)
    have h2W : 0<2*W.val := Rat.mul_pos (by decide +kernel) W.property
    let H : QPos := ⟨2*W.val*J.width,Rat.mul_pos h2W hwpos⟩
    have hH : H.val≤D.val := by
      have hp := Rat.mul_le_mul_of_nonneg_left (RationalMajorant.half_pow_le_one_div_succ N)
        (Rat.le_of_lt h2W)
      have hr := RationalMajorant.natRateStage_spec_of_le (Rat.le_of_lt h2W) D (Nat.le_refl N)
      change 2*W.val*J.width≤D.val
      rw [hw]
      have he : (2*W.val)*(1/((N+1:Nat):Rat))=(2*W.val)/((N+1:Nat):Rat) := by
        rw [Rat.div_def,Rat.div_def,Rat.one_mul]
      rw [he] at hp
      exact Rat.le_trans hp hr
    have ho := bisectionInterval_ordered (⟨0,1⟩ : QInterval) (by decide +kernel) choice N
    have he := bisectionInterval_nested (⟨0,1⟩ : QInterval) (by decide +kernel)
      choice 0 N (Nat.zero_le N)
    have near (u : Rat) (hulo : J.lo≤u) (huhi : u≤J.hi) :
        Small (sub (AffineSegment.point p q u).val a.val) H.val := by
      have hn := bisectionReal_stage_neighborhood (⟨0,1⟩ : QInterval)
        (by decide +kernel) choice N u hulo huhi
      exact representedAffine_rational_neighborhood p q t u
        (Rat.le_trans he.1 hulo) (Rat.le_trans huhi he.2.2) W.val J.width
        (Rat.le_of_lt W.property) (Rat.le_of_lt hwpos) hd hn.1 hn.2
    have hz := near J.hi ho Rat.le_refl
    have hl := near J.lo Rat.le_refl ho
    have hdisp := AffineSegment.difference_bound p q W.val J.lo J.hi hd
      (by change 0≤J.width; exact Rat.le_of_lt hwpos)
    have hv := pairedRiccati_local_endpoint_variation a
      (AffineSegment.point p q J.hi) (AffineSegment.point p q J.lo) H (J.width*W.val)
      (Rat.mul_nonneg (Rat.le_of_lt hwpos) (Rat.le_of_lt W.property)) hH hz hl hdisp
    refine ⟨N, ?_⟩
    apply hv.mono
    change 2854864384*(J.width*W.val)+2*W.val*J.width≤2854864386*W.val*J.width
    grind only
  have hg : Small (sub
      (pairedEntireRiccatiMap.eval (AffineSegment.point p q 1) trivial).val
      (pairedEntireRiccatiMap.eval (AffineSegment.point p q 0) trivial).val)
      (2854864386*W.val) := by
    have hw : (⟨0,1⟩ : QInterval).width=1 := by decide +kernel
    change Small _ (2854864386*W.val*(⟨0,1⟩ : QInterval).width) at good
    rw [hw,Rat.mul_one] at good
    exact good
  exact Small.congr
    (sub_valid (pairedEntireRiccatiMap.eval (AffineSegment.point p q 1) trivial).property
      (pairedEntireRiccatiMap.eval (AffineSegment.point p q 0) trivial).property)
    (sub_valid (pairedEntireRiccatiMap.eval q trivial).property (pairedEntireRiccatiMap.eval p trivial).property)
    (FunctionTheory.sub_congr
      (pairedEntireRiccatiMap.eval_congr _ _ trivial trivial (AffineSegment.point_one p q))
      (pairedEntireRiccatiMap.eval_congr _ _ trivial trivial (AffineSegment.point_zero p q))) hg

end ComputableAnalysis.ModularForms
