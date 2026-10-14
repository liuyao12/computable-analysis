import ComputableAnalysis.RiemannHilbert.ContourRectangleDomains

/-! Local linearized variation from actual domain-safe derivative evidence. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

theorem realNeighborhood_complex_displacement (x : RealRaw) (q r : Rat)
    (hr : 0≤r) (hl : RealRaw.Le (RealRaw.ofRat (q-r)) x)
    (hh : RealRaw.Le x (RealRaw.ofRat (q+r))) :
    Small (sub (ofRealRaw (RealRaw.ofRat q)) (ofRealRaw x)) r := by
  constructor
  · intro n m
    have hb := hh m 0
    change (x.compute m).lo ≤ q+r at hb
    change -r ≤ q + -(x.compute m).lo
    grind only
  · constructor
    · intro n m
      have hb := hl 0 n
      change q-r ≤ (x.compute n).hi at hb
      change q + -(x.compute n).hi ≤ r
      grind only
    · constructor <;> intro n m <;> change _ ≤ _ <;>
        simp [sub,add,neg,ofRealRaw,RealRaw.ofRat,imagPart,
          QBox.add,QBox.neg,QComplex.add] <;> grind only

theorem representedAffine_rational_neighborhood (p q : Scalar)
    (t : UnitInterval.Point) (u : Rat) (hu0 : 0≤u) (hu1 : u≤1)
    (W r : Rat) (hW : 0≤W) (hr : 0≤r)
    (hd : Small (AffineSegment.displacement p q).val W)
    (hl : RealRaw.Le (RealRaw.ofRat (u-r)) t.value)
    (hh : RealRaw.Le t.value (RealRaw.ofRat (u+r))) :
    Small (sub (AffineSegment.point p q u).val
      (RepresentedAffineSegment.point p q t).val) (2*W*r) := by
  have ht := realNeighborhood_complex_displacement t.value u r hr hl hh
  have hb := RepresentedAffineSegment.difference_bound p q t
    (UnitInterval.rational u hu0 hu1) W r hW hr hd ht
  exact Small.congr
    (sub_valid (RepresentedAffineSegment.point p q (UnitInterval.rational u hu0 hu1)).property
      (RepresentedAffineSegment.point p q t).property)
    (sub_valid (AffineSegment.point p q u).property (RepresentedAffineSegment.point p q t).property)
    (add_equiv
      (RepresentedAffineSegment.rational_agreement p q u hu0 hu1)
      (neg_equiv (equiv_refl _ (RepresentedAffineSegment.point p q t).property))) hb
theorem representedDifference_split (x y z : Scalar) :
    (add (sub x.val y.val) (sub y.val z.val)).Equiv (sub x.val z.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (sub_valid x.property y.property) (sub_valid y.property z.property))
    (hright := sub_valid x.property z.property)
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change (X-Y)+(Y-Z)=X-Z
  grind only
def domainLinearizedValue (f : DomainFunctions.Map) (d z : Scalar) (hz : f.domain z) : Scalar :=
  ⟨sub (f.eval z hz).val (mul d.val z.val),
    sub_valid (f.eval z hz).property (mul_valid d.property z.property)⟩

theorem domainLinearized_difference (f : DomainFunctions.Map) (d z w : Scalar)
    (hz : f.domain z) (hw : f.domain w) :
    (sub (domainLinearizedValue f d z hz).val (domainLinearizedValue f d w hw).val).Equiv
      (sub (sub (f.eval z hz).val
        (f.eval w hw).val) (mul d.val (sub z.val w.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (domainLinearizedValue f d z hz).property (domainLinearizedValue f d w hw).property)
    (hright := sub_valid
      (sub_valid (f.eval z hz).property (f.eval w hw).property)
      (mul_valid d.property (sub_valid z.property w.property)))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let FZ := ComplexRawQuotient.ofRaw (f.eval z hz).val
    (f.eval z hz).property
  let FW := ComplexRawQuotient.ofRaw (f.eval w hw).val
    (f.eval w hw).property
  change (FZ-D*Z)-(FW-D*W)=(FZ-FW)-D*(Z-W)
  grind only

theorem domainLinearized_local_variation (f : DomainFunctions.Map)
    (a D d z w : Scalar) (ha : f.domain a) (hz : f.domain z) (hw : f.domain w)
    (hf : HasDerivativeAt f a ha D) (eps eta H : QPos) (L : Rat) (hL : 0≤L)
    (hd : Small (sub D.val d.val) eps.val) (hH : H.val≤(hf.delta eta).val)
    (hza : Small (sub z.val a.val) H.val) (hwa : Small (sub w.val a.val) H.val)
    (hzw : Small (sub z.val w.val) L) :
    Small (sub (domainLinearizedValue f d z hz).val (domainLinearizedValue f d w hw).val)
      (2*eps.val*L+2*eta.val*H.val) := by
  have er := SeriesLimitLaws.small_sub (hf.estimate eta H z hz hH hza)
    (hf.estimate eta H w hw hH hwa)
  have hb := LocalODE.small_add
    (Small.mul (sub_valid D.property d.property) (sub_valid z.property w.property)
      (Rat.le_of_lt eps.property) hL hd hzw) er
  have he : (add (mul (sub D.val d.val) (sub z.val w.val))
      (sub (remainder f a ha D z hz)
        (remainder f a ha D w hw))).Equiv
      (sub (domainLinearizedValue f d z hz).val (domainLinearizedValue f d w hw).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (mul_valid (sub_valid D.property d.property) (sub_valid z.property w.property))
        (sub_valid (remainder_valid f a ha D z hz)
          (remainder_valid f a ha D w hw)))
      (hright := sub_valid (domainLinearizedValue f d z hz).property (domainLinearizedValue f d w hw).property)
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    let W := ComplexRawQuotient.ofRaw w.val w.property
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let D' := ComplexRawQuotient.ofRaw D.val D.property
    let d' := ComplexRawQuotient.ofRaw d.val d.property
    let FZ := ComplexRawQuotient.ofRaw (f.eval z hz).val
      (f.eval z hz).property
    let FW := ComplexRawQuotient.ofRaw (f.eval w hw).val
      (f.eval w hw).property
    let FA := ComplexRawQuotient.ofRaw (f.eval a ha).val
      (f.eval a ha).property
    change (D'-d')*(Z-W)+((FZ-FA-D'*(Z-A))-(FW-FA-D'*(W-A)))=
      (FZ-d'*Z)-(FW-d'*W)
    grind only
  have hs := Small.congr
    (add_valid (mul_valid (sub_valid D.property d.property) (sub_valid z.property w.property))
      (sub_valid (remainder_valid f a ha D z hz)
        (remainder_valid f a ha D w hw)))
    (sub_valid (domainLinearizedValue f d z hz).property (domainLinearizedValue f d w hw).property) he hb
  have hc : 2*eps.val*L+(eta.val*H.val+eta.val*H.val)=2*eps.val*L+2*eta.val*H.val := by grind only
  rw [hc] at hs
  exact hs

theorem domainLinearized_local_remainder_bound (f : DomainFunctions.Map)
    (a D d z w : Scalar) (ha : f.domain a) (hz : f.domain z) (hw : f.domain w)
    (hf : HasDerivativeAt f a ha D) (eps eta H : QPos) (L : Rat) (hL : 0≤L)
    (hd : Small (sub D.val d.val) eps.val) (hH : H.val≤(hf.delta eta).val)
    (hza : Small (sub z.val a.val) H.val) (hwa : Small (sub w.val a.val) H.val)
    (hzw : Small (sub z.val w.val) L) :
    Small (remainder f w hw d z hz) (2*eps.val*L+2*eta.val*H.val) :=
  Small.congr
    (sub_valid (domainLinearizedValue f d z hz).property (domainLinearizedValue f d w hw).property)
    (remainder_valid f w hw d z hz) (domainLinearized_difference f d z w hz hw)
    (domainLinearized_local_variation f a D d z w ha hz hw hf eps eta H L hL hd hH hza hwa hzw)

end ComputableAnalysis.RiemannHilbert.RectangularContour
