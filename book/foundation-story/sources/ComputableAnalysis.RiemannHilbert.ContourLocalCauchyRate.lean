import ComputableAnalysis.RiemannHilbert.ContourLocalCauchy

/-! An explicit local continuity and dyadic quadrature schedule beneath the
exact shrinking Cauchy identity. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem contour_half_rate (C : Rat) (hC : 0≤C) (eps : QPos) (n : Nat)
    (hn : RationalMajorant.natRateStage C eps≤n) : C*((1:Rat)/2)^n≤eps.val := by
  have hb := Rat.mul_le_mul_of_nonneg_left (RationalMajorant.half_pow_le_one_div_succ n) hC
  have hr := RationalMajorant.natRateStage_spec_of_le hC eps hn
  have he : C*(1/((n+1:Nat):Rat))=C/((n+1:Nat):Rat) := by simp only [Rat.div_def,Rat.one_mul]
  rw [he] at hb
  exact Rat.le_trans hb hr

theorem reciprocalInnerPrefix_geometric_error (R : QPos) (n : Nat) :
    Small (sub (reciprocalInnerPrefix R (2^n)).val rectangularPeriod.val) (16*((1:Rat)/2)^n) := by
  have hp := two_pow_half_pow n
  have hi := Rat.mul_inv_cancel ((2^n:Nat):Rat)
    (Rat.ne_of_gt (Rat.natCast_pos.mpr (Nat.two_pow_pos n)))
  have he : (16:Rat)/((2^n:Nat):Rat)=16*((1:Rat)/2)^n := by
    simp only [Rat.div_def]
    grind only
  rw [←he]
  exact reciprocalInnerPrefix_error R n

def localCauchyStage (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) : Nat :=
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  let theta := divideRadius eta (⟨64,by decide +kernel⟩ : QPos)
  max (contourErrorStage f hf a ha (hf.continuous.delta a ha theta))
    (RationalMajorant.natRateStage (32*scalarBound (f.eval a ha)) eta)

theorem localCauchyStage_spec (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a : Scalar) (ha : f.domain a) (eps : QPos) (n : Nat)
    (hn : localCauchyStage f hf a ha eps≤n) :
    Small (sub (localCauchyContour f hf a ha n).val (localCauchyValue f a ha).val) eps.val := by
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  let theta := divideRadius eta (⟨64,by decide +kernel⟩ : QPos)
  let r := shrinkingContourRadius f hf a ha n
  let p := shrinkingReciprocalPrefix f hf a ha n (2^n)
  let c := f.eval a ha
  have hnum : contourErrorStage f hf a ha (hf.continuous.delta a ha theta)≤n := by
    exact Nat.le_trans (Nat.le_max_left _ _) hn
  have hperiod : RationalMajorant.natRateStage (32*scalarBound c) eta≤n := by
    exact Nat.le_trans (Nat.le_max_right _ _) hn
  have hc := shrinkingPrefix_center_estimate f hf a ha theta n (2^n) (Nat.two_pow_pos n) hnum
  have he1 : 64*theta.val=eta.val := divideRadius_identity eta (⟨64,by decide +kernel⟩ : QPos)
  rw [he1] at hc
  have hp := reciprocalInnerPrefix_geometric_error r n
  have hm := Small.mul c.property (sub_valid p.property rectangularPeriod.property)
    (Rat.le_of_lt (scalarBound_pos c))
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.pow_pos (by decide +kernel))))
    (scalar_small c) hp
  have hC : 0≤32*scalarBound c := Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (scalarBound_pos c))
  have hrate := contour_half_rate (32*scalarBound c) hC eta n hperiod
  have hsize : 2*scalarBound c*(16*((1:Rat)/2)^n)=32*scalarBound c*((1:Rat)/2)^n := by grind only
  rw [hsize] at hm
  have hb := hm.mono hrate
  have hproduct := Small.congr (mul_valid c.property (sub_valid p.property rectangularPeriod.property))
    (sub_valid (scalarProduct c p).property (scalarProduct c rectangularPeriod).property)
    (equiv_symm (product_difference_left c p rectangularPeriod)) hb
  have hsum := LocalODE.small_add hc hproduct
  have heps : eta.val+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at h
    grind only
  rw [heps] at hsum
  have hs := Small.congr
    (add_valid (sub_valid (localCauchyContour f hf a ha n).property (scalarProduct c p).property)
      (sub_valid (scalarProduct c p).property (scalarProduct c rectangularPeriod).property))
    (sub_valid (localCauchyContour f hf a ha n).property (scalarProduct c rectangularPeriod).property)
    (representedDifference_split _ _ _) hsum
  have hg := mul_equiv c.property c.property rectangularPeriod.property geometricPeriod.property
    (equiv_refl _ c.property) rectangularPeriod_geometric
  exact Small.congr (sub_valid (localCauchyContour f hf a ha n).property (scalarProduct c rectangularPeriod).property)
    (sub_valid (localCauchyContour f hf a ha n).property (localCauchyValue f a ha).property)
    (FunctionTheory.sub_congr (equiv_refl _ (localCauchyContour f hf a ha n).property) hg) hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
