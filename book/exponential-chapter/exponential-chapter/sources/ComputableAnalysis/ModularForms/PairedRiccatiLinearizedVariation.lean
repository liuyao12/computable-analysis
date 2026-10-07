import ComputableAnalysis.ModularForms.PairedRiccatiGlobalSegmentVariation

/-! Segment linearization from justified derivative variation, without a
supplied partition or a uniform derivative radius. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def linearizedRiccatiValue (d z : Scalar) : Scalar :=
  ⟨sub (pairedEntireRiccatiMap.eval z trivial).val (mul d.val z.val),
    sub_valid (pairedEntireRiccatiMap.eval z trivial).property (mul_valid d.property z.property)⟩

theorem linearizedRiccati_difference (d z w : Scalar) :
    (sub (linearizedRiccatiValue d z).val (linearizedRiccatiValue d w).val).Equiv
      (sub (sub (pairedEntireRiccatiMap.eval z trivial).val
        (pairedEntireRiccatiMap.eval w trivial).val) (mul d.val (sub z.val w.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (linearizedRiccatiValue d z).property (linearizedRiccatiValue d w).property)
    (hright := sub_valid
      (sub_valid (pairedEntireRiccatiMap.eval z trivial).property (pairedEntireRiccatiMap.eval w trivial).property)
      (mul_valid d.property (sub_valid z.property w.property)))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let FZ := ComplexRawQuotient.ofRaw (pairedEntireRiccatiMap.eval z trivial).val
    (pairedEntireRiccatiMap.eval z trivial).property
  let FW := ComplexRawQuotient.ofRaw (pairedEntireRiccatiMap.eval w trivial).val
    (pairedEntireRiccatiMap.eval w trivial).property
  change (FZ-D*Z)-(FW-D*W)=(FZ-FW)-D*(Z-W)
  grind only

theorem linearizedRiccati_local_variation (a d z w : Scalar) (eps eta H : QPos)
    (L : Rat) (hL : 0≤L)
    (hd : Small (sub (pairedEntireRiccatiMap_holomorphic.derivative a trivial).val d.val) eps.val)
    (hH : H.val≤((pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta eta).val)
    (hz : Small (sub z.val a.val) H.val) (hw : Small (sub w.val a.val) H.val)
    (hzw : Small (sub z.val w.val) L) :
    Small (sub (linearizedRiccatiValue d z).val (linearizedRiccatiValue d w).val)
      (2*eps.val*L+2*eta.val*H.val) := by
  let D := pairedEntireRiccatiMap_holomorphic.derivative a trivial
  let hf := pairedEntireRiccatiMap_holomorphic.atPoint a trivial
  have er := SeriesLimitLaws.small_sub (hf.estimate eta H z trivial hH hz)
    (hf.estimate eta H w trivial hH hw)
  have hb := LocalODE.small_add
    (Small.mul (sub_valid D.property d.property) (sub_valid z.property w.property)
      (Rat.le_of_lt eps.property) hL hd hzw) er
  have he : (add (mul (sub D.val d.val) (sub z.val w.val))
      (sub (remainder pairedEntireRiccatiMap a trivial D z trivial)
        (remainder pairedEntireRiccatiMap a trivial D w trivial))).Equiv
      (sub (linearizedRiccatiValue d z).val (linearizedRiccatiValue d w).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (mul_valid (sub_valid D.property d.property) (sub_valid z.property w.property))
        (sub_valid (remainder_valid pairedEntireRiccatiMap a trivial D z trivial)
          (remainder_valid pairedEntireRiccatiMap a trivial D w trivial)))
      (hright := sub_valid (linearizedRiccatiValue d z).property (linearizedRiccatiValue d w).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let W := ComplexRawQuotient.ofRaw w.val w.property
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let D' := ComplexRawQuotient.ofRaw D.val D.property
    let d' := ComplexRawQuotient.ofRaw d.val d.property
    let FZ := ComplexRawQuotient.ofRaw (pairedEntireRiccatiMap.eval z trivial).val
      (pairedEntireRiccatiMap.eval z trivial).property
    let FW := ComplexRawQuotient.ofRaw (pairedEntireRiccatiMap.eval w trivial).val
      (pairedEntireRiccatiMap.eval w trivial).property
    let FA := ComplexRawQuotient.ofRaw (pairedEntireRiccatiMap.eval a trivial).val
      (pairedEntireRiccatiMap.eval a trivial).property
    change (D'-d')*(Z-W)+((FZ-FA-D'*(Z-A))-(FW-FA-D'*(W-A)))=
      (FZ-d'*Z)-(FW-d'*W)
    grind only
  have hs := Small.congr
    (add_valid (mul_valid (sub_valid D.property d.property) (sub_valid z.property w.property))
      (sub_valid (remainder_valid pairedEntireRiccatiMap a trivial D z trivial)
        (remainder_valid pairedEntireRiccatiMap a trivial D w trivial)))
    (sub_valid (linearizedRiccatiValue d z).property (linearizedRiccatiValue d w).property) he hb
  have hc : 2*eps.val*L+(eta.val*H.val+eta.val*H.val)=2*eps.val*L+2*eta.val*H.val := by grind only
  rw [hc] at hs
  exact hs

def linearizedRiccatiEndpointGood (p q d : Scalar) (eps W : Rat) (I : QInterval) : Prop :=
  Small (sub (linearizedRiccatiValue d (AffineSegment.point p q I.hi)).val
    (linearizedRiccatiValue d (AffineSegment.point p q I.lo)).val)
    (4*eps*W*I.width)

theorem linearizedRiccatiEndpointGood_join (p q d : Scalar) (eps W : Rat) (I : QInterval)
    (hl : linearizedRiccatiEndpointGood p q d eps W (bisectInterval I false))
    (hr : linearizedRiccatiEndpointGood p q d eps W (bisectInterval I true)) : linearizedRiccatiEndpointGood p q d eps W I := by
  have hb := LocalODE.small_add hr hl
  let A := linearizedRiccatiValue d (AffineSegment.point p q I.hi)
  let B := linearizedRiccatiValue d (AffineSegment.point p q I.midpoint)
  let C := linearizedRiccatiValue d (AffineSegment.point p q I.lo)
  have hs := Small.congr
    (add_valid (sub_valid A.property B.property) (sub_valid B.property C.property))
    (sub_valid A.property C.property) (representedDifference_split A B C) hb
  have he : 4*eps*W*(bisectInterval I true).width+
      4*eps*W*(bisectInterval I false).width=4*eps*W*I.width := by
    rw [bisectInterval_width,bisectInterval_width]
    grind only
  rw [he] at hs
  exact hs

theorem pairedRiccati_segment_linearization (p q d : Scalar) (W eps : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (hder : ∀ t : UnitInterval.Point,
      Small (sub (pairedEntireRiccatiMap_holomorphic.derivative
        (RepresentedAffineSegment.point p q t) trivial).val d.val) eps.val) :
    Small (sub (linearizedRiccatiValue d q).val
      (linearizedRiccatiValue d p).val) (4*eps.val*W.val) := by
  have good : linearizedRiccatiEndpointGood p q d eps.val W.val ⟨0,1⟩ := by
    apply bisection_cover_principle (linearizedRiccatiEndpointGood p q d eps.val W.val) ⟨0,1⟩
      (linearizedRiccatiEndpointGood_join p q d eps.val W.val)
    intro choice
    have hx := bisectionReal_enclosed (⟨0,1⟩ : QInterval) (by decide +kernel) choice 0
    let t : UnitInterval.Point := ⟨bisectionReal ⟨0,1⟩ choice,
      bisectionReal_valid ⟨0,1⟩ (by decide +kernel) choice,hx.1,hx.2⟩
    let a := RepresentedAffineSegment.point p q t
    let eta : QPos := ⟨eps.val/2,by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (by decide +kernel)⟩
    let D := (pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta eta
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
    have hv := linearizedRiccati_local_variation a d
      (AffineSegment.point p q J.hi) (AffineSegment.point p q J.lo) eps eta H (J.width*W.val)
      (Rat.mul_nonneg (Rat.le_of_lt hwpos) (Rat.le_of_lt W.property)) (hder t) hH hz hl hdisp
    refine ⟨N, ?_⟩
    apply hv.mono
    change 2*eps.val*(J.width*W.val)+2*(eps.val/2)*(2*W.val*J.width)≤4*eps.val*W.val*J.width
    grind only
  have hg : Small (sub
      (linearizedRiccatiValue d (AffineSegment.point p q 1)).val
      (linearizedRiccatiValue d (AffineSegment.point p q 0)).val)
      (4*eps.val*W.val) := by
    have hw : (⟨0,1⟩ : QInterval).width=1 := by decide +kernel
    change Small _ (4*eps.val*W.val*(⟨0,1⟩ : QInterval).width) at good
    rw [hw,Rat.mul_one] at good
    exact good
  have congrValue (z w : Scalar) (he : z.val.Equiv w.val) :
      (linearizedRiccatiValue d z).val.Equiv (linearizedRiccatiValue d w).val :=
    FunctionTheory.sub_congr (pairedEntireRiccatiMap.eval_congr z w trivial trivial he)
      (ComplexRaw.mul_equiv d.property d.property z.property w.property
        (equiv_refl d.val d.property) he)
  exact Small.congr
    (sub_valid (linearizedRiccatiValue d (AffineSegment.point p q 1)).property
      (linearizedRiccatiValue d (AffineSegment.point p q 0)).property)
    (sub_valid (linearizedRiccatiValue d q).property (linearizedRiccatiValue d p).property)
    (FunctionTheory.sub_congr
      (congrValue _ _ (AffineSegment.point_one p q))
      (congrValue _ _ (AffineSegment.point_zero p q))) hg

theorem pairedRiccati_segment_linearization_error (p q d : Scalar) (W eps : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (hder : ∀ t : UnitInterval.Point,
      Small (sub (pairedEntireRiccatiMap_holomorphic.derivative
        (RepresentedAffineSegment.point p q t) trivial).val d.val) eps.val) :
    Small (remainder pairedEntireRiccatiMap p trivial d q trivial)
      (4*eps.val*W.val) :=
  Small.congr (sub_valid (linearizedRiccatiValue d q).property (linearizedRiccatiValue d p).property)
    (remainder_valid pairedEntireRiccatiMap p trivial d q trivial)
    (linearizedRiccati_difference d q p)
    (pairedRiccati_segment_linearization p q d W eps hd hder)

theorem pairedRiccati_neighborhood_linearization (a p q : Scalar) (W eps : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (hp : Small (Centered.offset a p).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val)
    (hq : Small (Centered.offset a q).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val) :
    Small (remainder pairedEntireRiccatiMap p trivial
      (pairedEntireRiccatiMap_holomorphic.derivative a trivial) q trivial)
      (4*eps.val*W.val) := by
  apply pairedRiccati_segment_linearization_error p q _ W eps hd
  intro t
  exact pairedEntireRiccatiMap_holomorphic.continuousDerivative.estimate a trivial eps
    (RepresentedAffineSegment.point p q t) trivial
    (RepresentedAffineSegment.offset_bound a p q t _ hp hq)

end ComputableAnalysis.ModularForms
