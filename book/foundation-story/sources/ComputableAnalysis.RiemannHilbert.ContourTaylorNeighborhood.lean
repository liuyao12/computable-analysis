import ComputableAnalysis.RiemannHilbert.ContourTaylorRemainder

/-! A computed neighborhood on which all Taylor kernel estimates apply.
Callers need only their actual holomorphic map and represented base point. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def localCauchyTaylorRadius (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) : QPos :=
  divideRadius (effectiveLocalRadius f hf b hb) ⟨256,by decide +kernel⟩

theorem localCauchyTaylorRadius_identity (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    256*(localCauchyTaylorRadius f hf b hb).val=(effectiveLocalRadius f hf b hb).val :=
  divideRadius_identity (effectiveLocalRadius f hf b hb) (⟨256,by decide +kernel⟩ : QPos)

theorem localCauchyCoefficientRate_identity (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    (effectiveLocalRadius f hf b hb).val*(localCauchyCoefficientRate f hf b hb).val=16 := by
  have hn := Rat.ne_of_gt (effectiveLocalRadius f hf b hb).property
  dsimp [localCauchyCoefficientRate,centeredBoundaryReciprocalBound]
  have hc := Rat.div_mul_cancel (a := (8:Rat)) hn
  grind only

theorem localCauchyTaylorRadius_rate (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    (localCauchyCoefficientRate f hf b hb).val*(localCauchyTaylorRadius f hf b hb).val=(1:Rat)/16 := by
  have hR := localCauchyTaylorRadius_identity f hf b hb
  have hK := localCauchyCoefficientRate_identity f hf b hb
  grind only

theorem localCauchyTaylorRadius_kernel_budget (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b) :
    16*(centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)).val*(localCauchyTaylorRadius f hf b hb).val≤1 := by
  have h := localCauchyTaylorRadius_rate f hf b hb
  change (2*(centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)).val)*
    (localCauchyTaylorRadius f hf b hb).val=(1:Rat)/16 at h
  rw [show 16*(centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)).val*
      (localCauchyTaylorRadius f hf b hb).val=8*(2*(centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)).val*
        (localCauchyTaylorRadius f hf b hb).val) by grind only,h]
  decide +kernel

theorem localCauchyTaylorRadius_domain (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : Small (Centered.offset b z).val (localCauchyTaylorRadius f hf b hb).val) : f.domain z := by
  have hR := localCauchyTaylorRadius_identity f hf b hb
  have hr := divideRadius_identity (localHolomorphicRadius f hf b hb) (⟨4,by decide +kernel⟩ : QPos)
  change 4*(effectiveLocalRadius f hf b hb).val=(localHolomorphicRadius f hf b hb).val at hr
  have hp := (localCauchyTaylorRadius f hf b hb).property
  exact localHolomorphic_domain f hf b hb z (hz.mono (by grind only))

theorem localCauchyTaylorRadius_pole_inside (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : Small (Centered.offset b z).val (localCauchyTaylorRadius f hf b hb).val) :
    RectanglePoleInterior (effectiveLocalRectangle f hf b hb) z := by
  let R := effectiveLocalRadius f hf b hb
  let c := representedPoleCenter b R 0
  let D : QPos := ⟨R.val/2,by rw [Rat.div_def]; exact Rat.mul_pos R.property (by decide +kernel)⟩
  have hc := (rationalPoleCenter_error b R 0).mono (poleCenterTolerance_relative R 0)
  have hs := LocalODE.small_add hz hc
  have hnear : Small (Centered.offset c z).val ((localCauchyTaylorRadius f hf b hb).val+R.val/64) :=
    Small.congr (add_valid (Centered.offset b z).property (Centered.offset c b).property)
      (Centered.offset c z).property (representedDifference_split z b c) hs
  have hR := localCauchyTaylorRadius_identity f hf b hb
  have hp := R.property
  have hhalf : Small (Centered.offset c z).val (R.val/2) := hnear.mono (by change 256*(localCauchyTaylorRadius f hf b hb).val=R.val at hR; grind only)
  refine ⟨D,?_⟩
  have hx (x : Rat) : x-R.val+D.val=x-R.val/2 := by dsimp [D]; grind only
  have hy (x : Rat) : x+R.val-D.val=x+R.val/2 := by dsimp [D]; grind only
  change representedRectangleContains
    (⟨(rationalPoleCenter b R 0).re-R.val+D.val,(rationalPoleCenter b R 0).re+R.val-D.val⟩,
      ⟨(rationalPoleCenter b R 0).im-R.val+D.val,(rationalPoleCenter b R 0).im+R.val-D.val⟩) z
  simpa only [rationalCenteredRectangle,hx,hy] using rationalCenteredRectangle_mem (rationalPoleCenter b R 0) z (R.val/2) hhalf

/-- Uniform finite Taylor error with all contour data constructed internally. -/
theorem localCauchyMomentPrefix_error (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : Small (Centered.offset b z).val (localCauchyTaylorRadius f hf b hb).val)
    (hza : f.domain z) (N : Nat) :
    Small (sub (f.eval z hza).val (cauchyMomentPrefix f hf b hb z N).val)
      (16*(localCauchyCoefficientBound f b hb).val*((1:Rat)/8)^N) := by
  let J := effectiveLocalRectangle f hf b hb
  let hd := effectiveLocalRectangle_domain f hf b hb
  let hp := effectiveLocalRectangle_pole_inside f hf b hb
  let hzJ := localCauchyTaylorRadius_pole_inside f hf b hb z hz
  have ho := rectanglePoleInterior_ordered J b hp
  let hdF := rectangleBoundaryDomains_of_rectangle f J ho.1 ho.2 hd
  let hdR := rectanglePoleReciprocalBoundaryDomains J b hp
  let F := localHolomorphicValueBound f b hb
  let U := centeredBoundaryReciprocalBound (effectiveLocalRadius f hf b hb)
  let H := localCauchyTaylorRadius f hf b hb
  have hs := cauchyMomentPrefix_error f hf J hd b z hp hzJ hb hza hdF hdR F U H
    (effectiveLocalRectangle_value_bound f hf b hb hdF) (effectiveLocalRectangle_reciprocal_bound f hf b hb hdR)
    hz (localCauchyTaylorRadius_kernel_budget f hf b hb) N
  have hR := localCauchyCoefficientRate_identity f hf b hb
  change (effectiveLocalRadius f hf b hb).val*(2*U.val)=16 at hR
  have hT := localCauchyTaylorRadius_rate f hf b hb
  change (2*U.val)*H.val=(1:Rat)/16 at hT
  have hq : 4*H.val*U.val=(1:Rat)/8 := by grind only
  have hw : J.1.width+J.2.width=4*(effectiveLocalRadius f hf b hb).val := by
    dsimp [J,effectiveLocalRectangle,rationalCenteredRectangle,QInterval.width]; grind only
  have he : 256*scalarBound inverseGeometricPeriod*(J.1.width+J.2.width)*F.val*U.val*(4*H.val*U.val)^N=
      16*(localCauchyCoefficientBound f b hb).val*((1:Rat)/8)^N := by
    rw [hq,hw]; dsimp [localCauchyCoefficientBound,F]; grind only
  rw [he] at hs
  exact hs

theorem localCauchyMomentPrefix_converges (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) (hb : f.domain b)
    (z : Scalar) (hz : Small (Centered.offset b z).val (localCauchyTaylorRadius f hf b hb).val) (hza : f.domain z) :
    Converges (cauchyMomentPrefix f hf b hb z) (f.eval z hza) := by
  have he := LocalODE.tail_bound_shrinks (4*(localCauchyCoefficientBound f b hb).val) ((1:Rat)/8)
    (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) (localCauchyCoefficientBound f b hb).property))
    (by decide +kernel) (by decide +kernel)
  intro eps
  obtain ⟨N,hN⟩ := he eps
  refine ⟨N,fun n hn => ?_⟩
  have hs := RepresentedCauchySum.small_sub_symm _ _ _ (localCauchyMomentPrefix_error f hf b hb z hz hza n)
  exact hs.mono (by have h := hN n hn; grind only)

end ComputableAnalysis.RiemannHilbert.RectangularContour
