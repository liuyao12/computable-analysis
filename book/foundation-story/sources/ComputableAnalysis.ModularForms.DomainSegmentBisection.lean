import ComputableAnalysis.ModularForms.DomainLinearizedVariation

/-! Domain evidence and endpoint telescoping for represented segment bisection.
No values outside the supplied domain are evaluated. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem affineSegment_domain_at (f : DomainFunctions.Map) (p q : Scalar)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (u : Rat) (hu0 : 0≤u) (hu1 : u≤1) : f.domain (AffineSegment.point p q u) :=
  (f.domain_congr _ _ (RepresentedAffineSegment.rational_agreement p q u hu0 hu1)).mp
    (hdom (UnitInterval.rational u hu0 hu1))

theorem domainLinearizedValue_congr (f : DomainFunctions.Map) (d z w : Scalar)
    (hz : f.domain z) (hw : f.domain w) (he : z.val.Equiv w.val) :
    (domainLinearizedValue f d z hz).val.Equiv (domainLinearizedValue f d w hw).val :=
  FunctionTheory.sub_congr (f.eval_congr z w hz hw he)
    (mul_equiv d.property d.property z.property w.property (equiv_refl _ d.property) he)

def domainLinearizedEndpointGood (f : DomainFunctions.Map) (p q d : Scalar)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (eps W : Rat) (I : QInterval) : Prop :=
  ∀ hI : I.lo≤I.hi, ∀ h0 : 0≤I.lo, ∀ h1 : I.hi≤1,
    Small (sub
      (domainLinearizedValue f d (AffineSegment.point p q I.hi)
        (affineSegment_domain_at f p q hdom I.hi (Rat.le_trans h0 hI) h1)).val
      (domainLinearizedValue f d (AffineSegment.point p q I.lo)
        (affineSegment_domain_at f p q hdom I.lo h0 (Rat.le_trans hI h1))).val)
      (4*eps*W*I.width)

theorem domainLinearizedEndpointGood_join (f : DomainFunctions.Map) (p q d : Scalar)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (eps W : Rat) (I : QInterval)
    (hl : domainLinearizedEndpointGood f p q d hdom eps W (bisectInterval I false))
    (hr : domainLinearizedEndpointGood f p q d hdom eps W (bisectInterval I true)) :
    domainLinearizedEndpointGood f p q d hdom eps W I := by
  intro hI h0 h1
  have bl := bisectInterval_bounds I hI false
  have br := bisectInterval_bounds I hI true
  have hlb := hl bl.2.1 (Rat.le_trans h0 bl.1) (Rat.le_trans bl.2.2 h1)
  have hrb := hr br.2.1 (Rat.le_trans h0 br.1) (Rat.le_trans br.2.2 h1)
  have hm := midpoint_mem I hI
  let A := domainLinearizedValue f d (AffineSegment.point p q I.hi)
    (affineSegment_domain_at f p q hdom I.hi (Rat.le_trans h0 hI) h1)
  let B := domainLinearizedValue f d (AffineSegment.point p q I.midpoint)
    (affineSegment_domain_at f p q hdom I.midpoint (Rat.le_trans h0 hm.1) (Rat.le_trans hm.2 h1))
  let C := domainLinearizedValue f d (AffineSegment.point p q I.lo)
    (affineSegment_domain_at f p q hdom I.lo h0 (Rat.le_trans hI h1))
  change Small (sub B.val C.val) (4*eps*W*(bisectInterval I false).width) at hlb
  change Small (sub A.val B.val) (4*eps*W*(bisectInterval I true).width) at hrb
  have hb := LocalODE.small_add hrb hlb
  have hs := Small.congr
    (add_valid (sub_valid A.property B.property) (sub_valid B.property C.property))
    (sub_valid A.property C.property) (representedDifference_split A B C) hb
  have he : 4*eps*W*(bisectInterval I true).width+
      4*eps*W*(bisectInterval I false).width=4*eps*W*I.width := by
    rw [bisectInterval_width,bisectInterval_width]
    grind only
  rw [he] at hs
  exact hs

theorem domainSegment_linearized_difference_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (p q d : Scalar) (hp : f.domain p) (hq : f.domain q) (W eps : QPos)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (hder : ∀ t : UnitInterval.Point,
      Small (sub (hf.derivative (RepresentedAffineSegment.point p q t) (hdom t)).val d.val) eps.val) :
    Small (sub (domainLinearizedValue f d q hq).val (domainLinearizedValue f d p hp).val)
      (4*eps.val*W.val) := by
  have good : domainLinearizedEndpointGood f p q d hdom eps.val W.val ⟨0,1⟩ := by
    apply bisection_cover_principle (domainLinearizedEndpointGood f p q d hdom eps.val W.val) ⟨0,1⟩
      (domainLinearizedEndpointGood_join f p q d hdom eps.val W.val)
    intro choice
    have hx := bisectionReal_enclosed (⟨0,1⟩ : QInterval) (by decide +kernel) choice 0
    let t : UnitInterval.Point := ⟨bisectionReal ⟨0,1⟩ choice,
      bisectionReal_valid ⟨0,1⟩ (by decide +kernel) choice,hx.1,hx.2⟩
    let a := RepresentedAffineSegment.point p q t
    let eta : QPos := ⟨eps.val/2,by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (by decide +kernel)⟩
    let D := (hf.atPoint a (hdom t)).delta eta
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
    have hzdom := affineSegment_domain_at f p q hdom J.hi
      (Rat.le_trans he.1 ho) he.2.2
    have hwdom := affineSegment_domain_at f p q hdom J.lo he.1
      (Rat.le_trans ho he.2.2)
    have hv := domainLinearized_local_variation f a (hf.derivative a (hdom t)) d
      (AffineSegment.point p q J.hi) (AffineSegment.point p q J.lo)
      (hdom t) hzdom hwdom (hf.atPoint a (hdom t)) eps eta H (J.width*W.val)
      (Rat.mul_nonneg (Rat.le_of_lt hwpos) (Rat.le_of_lt W.property)) (hder t) hH hz hl hdisp
    refine ⟨N, ?_⟩
    intro hJ hJ0 hJ1
    apply hv.mono
    change 2*eps.val*(J.width*W.val)+2*(eps.val/2)*(2*W.val*J.width)≤4*eps.val*W.val*J.width
    grind only
  have hg : Small (sub
      (domainLinearizedValue f d (AffineSegment.point p q 1)
        (affineSegment_domain_at f p q hdom 1 (by decide +kernel) (by decide +kernel))).val
      (domainLinearizedValue f d (AffineSegment.point p q 0)
        (affineSegment_domain_at f p q hdom 0 (by decide +kernel) (by decide +kernel))).val)
      (4*eps.val*W.val) := by
    have hw : (⟨0,1⟩ : QInterval).width=1 := by decide +kernel
    have good := good (by decide +kernel) (by decide +kernel) (by decide +kernel)
    change Small _ (4*eps.val*W.val*(⟨0,1⟩ : QInterval).width) at good
    rw [hw,Rat.mul_one] at good
    exact good
  let Z := AffineSegment.point p q 1
  let A := AffineSegment.point p q 0
  have hz := affineSegment_domain_at f p q hdom 1 (by decide +kernel) (by decide +kernel)
  have ha := affineSegment_domain_at f p q hdom 0 (by decide +kernel) (by decide +kernel)
  exact Small.congr
    (sub_valid (domainLinearizedValue f d Z hz).property (domainLinearizedValue f d A ha).property)
    (sub_valid (domainLinearizedValue f d q hq).property (domainLinearizedValue f d p hp).property)
    (FunctionTheory.sub_congr
      (domainLinearizedValue_congr f d Z q hz hq (AffineSegment.point_one p q))
      (domainLinearizedValue_congr f d A p ha hp (AffineSegment.point_zero p q))) hg

theorem domainSegment_remainder_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (p q d : Scalar) (hp : f.domain p) (hq : f.domain q) (W eps : QPos)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (hder : ∀ t : UnitInterval.Point,
      Small (sub (hf.derivative (RepresentedAffineSegment.point p q t) (hdom t)).val d.val) eps.val) :
    Small (remainder f p hp d q hq) (4*eps.val*W.val) :=
  Small.congr (sub_valid (domainLinearizedValue f d q hq).property (domainLinearizedValue f d p hp).property)
    (remainder_valid f p hp d q hq) (domainLinearized_difference f d q p hq hp)
    (domainSegment_linearized_difference_bound f hf p q d hp hq W eps hdom hd hder)

end ComputableAnalysis.ModularForms
