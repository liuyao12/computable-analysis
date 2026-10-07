import ComputableAnalysis.ModularForms.PairedEntireGlobalDerivativeBound

/-! Two endpoints can be compared through one actual derivative center.
This is the local estimate needed to rule out a failing bisection path. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def halfDerivativeError : QPos := ⟨1/2,by decide +kernel⟩

theorem difference_through_derivative_remainders (f : DomainFunctions.Map)
    (a d z w : Scalar) (ha : f.domain a) (hz : f.domain z) (hw : f.domain w) :
    (sub (f.eval z hz).val (f.eval w hw).val).Equiv
      (add (mul d.val (sub z.val w.val))
        (sub (remainder f a ha d z hz) (remainder f a ha d w hw))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (f.eval z hz).property (f.eval w hw).property)
    (hright := add_valid (mul_valid d.property (sub_valid z.property w.property))
      (sub_valid (remainder_valid f a ha d z hz) (remainder_valid f a ha d w hw)))
  let Z := ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property
  let W := ComplexRawQuotient.ofRaw (f.eval w hw).val (f.eval w hw).property
  let A := ComplexRawQuotient.ofRaw (f.eval a ha).val (f.eval a ha).property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let z' := ComplexRawQuotient.ofRaw z.val z.property
  let w' := ComplexRawQuotient.ofRaw w.val w.property
  let a' := ComplexRawQuotient.ofRaw a.val a.property
  change Z-W=D*(z'-w')+((Z-A-D*(z'-a'))-(W-A-D*(w'-a')))
  grind only

theorem pairedRiccati_local_endpoint_variation (a z w : Scalar) (H : QPos)
    (L : Rat) (hL : 0≤L)
    (hH : H.val≤((pairedEntireRiccatiMap_holomorphic.atPoint a trivial).delta halfDerivativeError).val)
    (hz : Small (sub z.val a.val) H.val) (hw : Small (sub w.val a.val) H.val)
    (hzw : Small (sub z.val w.val) L) :
    Small (sub (pairedEntireRiccatiMap.eval z trivial).val
      (pairedEntireRiccatiMap.eval w trivial).val) (2854864384*L+H.val) := by
  let d := pairedEntireRiccatiMap_holomorphic.derivative a trivial
  let hf := pairedEntireRiccatiMap_holomorphic.atPoint a trivial
  have erz := hf.estimate halfDerivativeError H z trivial hH hz
  have erw := hf.estimate halfDerivativeError H w trivial hH hw
  have er := SeriesLimitLaws.small_sub erz erw
  have hd := Small.mul d.property (sub_valid z.property w.property)
    (by decide +kernel : (0:Rat)≤1427432192) hL
    (pairedEntireRiccatiMap_global_derivative_bound a) hzw
  have hb := LocalODE.small_add hd er
  have he := difference_through_derivative_remainders pairedEntireRiccatiMap a d z w trivial trivial trivial
  have hs := Small.congr
    (add_valid (mul_valid d.property (sub_valid z.property w.property))
      (sub_valid (remainder_valid pairedEntireRiccatiMap a trivial d z trivial)
        (remainder_valid pairedEntireRiccatiMap a trivial d w trivial)))
    (sub_valid (pairedEntireRiccatiMap.eval z trivial).property (pairedEntireRiccatiMap.eval w trivial).property)
    (equiv_symm he) hb
  have hc : 2*1427432192*L+
      (halfDerivativeError.val*H.val+halfDerivativeError.val*H.val)=2854864384*L+H.val := by
    unfold halfDerivativeError
    grind only
  rw [hc] at hs
  exact hs

end ComputableAnalysis.ModularForms
