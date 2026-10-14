import ComputableAnalysis.RiemannHilbert.ContourDisplacedCenters

/-! The actual shrinking rational square around any represented pole has the
center-times-geometric-period limit. Rational-center choices are internal. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def displacedLocalCauchyContour (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (n : Nat) : Scalar :=
  let R := shrinkingContourRadius f hf b hb n
  displacedInnerPrefix f b (displacedLocalCenter f hf b hb n) R
    (displacedLocalFrame_domain f hf b hb n)
    ((rationalPoleCenter_error b R n).mono (poleCenterTolerance_relative R n)) (2^n)

def displacedLocalCauchyStage (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (eps : QPos) : Nat :=
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  let theta := divideRadius eta (⟨128,by decide +kernel⟩ : QPos)
  max (displacedContourErrorStage f hf b hb (hf.continuous.delta b hb theta))
    (RationalMajorant.natRateStage (96*scalarBound (f.eval b hb)) eta)

theorem displacedLocalCauchyStage_spec (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (eps : QPos) (n : Nat)
    (hn : displacedLocalCauchyStage f hf b hb eps≤n) :
    Small (sub (displacedLocalCauchyContour f hf b hb n).val (localCauchyValue f b hb).val) eps.val := by
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  let theta := divideRadius eta (⟨128,by decide +kernel⟩ : QPos)
  let R := shrinkingContourRadius f hf b hb n
  let c := displacedLocalCenter f hf b hb n
  let A := f.eval b hb
  let P := reciprocalInnerPrefix R (2^n)
  let K := displacedLocalCauchyContour f hf b hb n
  have hn1 : displacedContourErrorStage f hf b hb (hf.continuous.delta b hb theta)≤n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : RationalMajorant.natRateStage (96*scalarBound A) eta≤n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hnum := displacedInnerPrefix_center_estimate f b c hb R (displacedLocalFrame_domain f hf b hb n)
    (poleCenterTolerance R n).val (Rat.le_of_lt (poleCenterTolerance R n).property)
    (poleCenterTolerance_relative R n) (rationalPoleCenter_error b R n) theta
    (displacedLocalFrame_numerator_close f hf b hb theta n hn1) (2^n) (Nat.two_pow_pos n)
  have hperiod := reciprocalInnerPrefix_geometric_error R n
  have hpower : 0≤((1:Rat)/2)^n := Rat.le_of_lt (Rat.pow_pos (by decide +kernel))
  have hper := Small.mul A.property (sub_valid P.property rectangularPeriod.property)
    (Rat.le_of_lt (scalarBound_pos A)) (Rat.mul_nonneg (by decide +kernel) hpower) (scalar_small A) hperiod
  have hs := Small.congr (mul_valid A.property (sub_valid P.property rectangularPeriod.property))
    (sub_valid (scalarProduct A P).property (scalarProduct A rectangularPeriod).property)
    (equiv_symm (product_difference_left A P rectangularPeriod)) hper
  have hsum := LocalODE.small_add hnum hs
  have hi := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
  have htheta : 128*theta.val=eta.val := divideRadius_identity eta (⟨128,by decide +kernel⟩ : QPos)
  have he : (128*theta.val+4096*scalarBound A*(poleCenterTolerance R n).val/R.val)+
      2*scalarBound A*(16*((1:Rat)/2)^n)=eta.val+96*scalarBound A*((1:Rat)/2)^n := by
    simp only [poleCenterTolerance,Rat.div_def]
    grind only
  rw [he] at hsum
  have hC : 0≤96*scalarBound A := Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (scalarBound_pos A))
  have hrate := contour_half_rate (96*scalarBound A) hC eta n hn2
  have heps : eta.val+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at h
    grind only
  have hbound : eta.val+96*scalarBound A*((1:Rat)/2)^n≤eps.val := by grind only
  have htotal := Small.congr
    (add_valid (sub_valid K.property (scalarProduct A P).property)
      (sub_valid (scalarProduct A P).property (scalarProduct A rectangularPeriod).property))
    (sub_valid K.property (scalarProduct A rectangularPeriod).property)
    (representedDifference_split K (scalarProduct A P) (scalarProduct A rectangularPeriod)) (hsum.mono hbound)
  exact Small.congr (sub_valid K.property (scalarProduct A rectangularPeriod).property)
    (sub_valid K.property (localCauchyValue f b hb).property)
    (FunctionTheory.sub_congr (equiv_refl _ K.property)
      (mul_equiv A.property A.property rectangularPeriod.property geometricPeriod.property
        (equiv_refl _ A.property) rectangularPeriod_geometric)) htotal

theorem displacedLocalCauchyContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) :
    Converges (displacedLocalCauchyContour f hf b hb) (localCauchyValue f b hb) :=
  fun eps => ⟨displacedLocalCauchyStage f hf b hb eps,
    fun n hn => displacedLocalCauchyStage_spec f hf b hb eps n hn⟩

theorem displacedLocalCauchyContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (u : Scalar)
    (hu : Converges (displacedLocalCauchyContour f hf b hb) u) : u≈localCauchyValue f b hb :=
  converge_unique _ _ _ hu (displacedLocalCauchyContour_converges f hf b hb)

theorem displacedLocalCauchy_center_limits_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (b c : Scalar) (hb : f.domain b) (hc : f.domain c) (he : b≈c) (u v : Scalar)
    (hu : Converges (displacedLocalCauchyContour f hf b hb) u)
    (hv : Converges (displacedLocalCauchyContour f hg c hc) v) : u≈v :=
  Setoid.trans (displacedLocalCauchyContour_limit_identity f hf b hb u hu)
    (Setoid.trans (localCauchyValue_congr f b c hb hc he)
      (Setoid.symm (displacedLocalCauchyContour_limit_identity f hg c hc v hv)))

theorem displaced_centered_shrinking_limits_agree (f : DomainFunctions.Map) (hf hg : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (u v : Scalar)
    (hu : Converges (displacedLocalCauchyContour f hf b hb) u)
    (hv : Converges (localCauchyContour f hg b hb) v) : u≈v :=
  Setoid.trans (displacedLocalCauchyContour_limit_identity f hf b hb u hu)
    (Setoid.symm (localCauchyContour_limit_identity f hg b hb v hv))

end ComputableAnalysis.RiemannHilbert.RectangularContour
