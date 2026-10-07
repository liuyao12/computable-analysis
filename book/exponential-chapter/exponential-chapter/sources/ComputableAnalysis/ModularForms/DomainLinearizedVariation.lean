import ComputableAnalysis.ModularForms.PunctureSafeAffineSegments
import ComputableAnalysis.ModularForms.PairedRiccatiLinearizedVariation

/-! Local linearization on a supplied domain, with actual derivative evidence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

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

theorem puncturedRiccati_local_remainder_bound (c a d z w : Scalar)
    (ha : NonzeroBoxSearch.Nonzero a) (hz : NonzeroBoxSearch.Nonzero z) (hw : NonzeroBoxSearch.Nonzero w)
    (eps eta H : QPos) (L : Rat) (hL : 0≤L)
    (hd : Small (sub ((pairedRiccatiCauchyIntegrandMap_holomorphic c).derivative a ha).val d.val) eps.val)
    (hH : H.val≤(((pairedRiccatiCauchyIntegrandMap_holomorphic c).atPoint a ha).delta eta).val)
    (hza : Small (sub z.val a.val) H.val) (hwa : Small (sub w.val a.val) H.val)
    (hzw : Small (sub z.val w.val) L) :
    Small (remainder (pairedRiccatiCauchyIntegrandMap c) w hw d z hz)
      (2*eps.val*L+2*eta.val*H.val) :=
  domainLinearized_local_remainder_bound (pairedRiccatiCauchyIntegrandMap c) a
    ((pairedRiccatiCauchyIntegrandMap_holomorphic c).derivative a ha) d z w ha hz hw
    ((pairedRiccatiCauchyIntegrandMap_holomorphic c).atPoint a ha)
    eps eta H L hL hd hH hza hwa hzw

end ComputableAnalysis.ModularForms
