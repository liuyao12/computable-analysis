import ComputableAnalysis.ModularForms.PairedRiccatiLocalEndpointVariation

/-! Two actual domain-map endpoints compared through a justified derivative
center. This is the local step for represented rational bisection. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- A genuine derivative bound at the center, with actual derivative
remainders, controls two endpoints in its local error neighborhood. -/
theorem domain_local_endpoint_variation (f : DomainFunctions.Map)
    (a z w d : Scalar) (ha : f.domain a) (hz : f.domain z) (hw : f.domain w)
    (hf : HasDerivativeAt f a ha d) (B L : Rat) (hB : 0≤B) (hL : 0≤L)
    (hd : Small d.val B) (H : QPos)
    (hH : H.val≤(hf.delta halfDerivativeError).val)
    (hza : Small (sub z.val a.val) H.val) (hwa : Small (sub w.val a.val) H.val)
    (hzw : Small (sub z.val w.val) L) :
    Small (sub (f.eval z hz).val (f.eval w hw).val) (2*B*L+H.val) := by
  have erz := hf.estimate halfDerivativeError H z hz hH hza
  have erw := hf.estimate halfDerivativeError H w hw hH hwa
  have er := SeriesLimitLaws.small_sub erz erw
  have hslope := Small.mul d.property (sub_valid z.property w.property) hB hL hd hzw
  have hb := LocalODE.small_add hslope er
  have he := difference_through_derivative_remainders f a d z w ha hz hw
  have hs := Small.congr
    (add_valid (mul_valid d.property (sub_valid z.property w.property))
      (sub_valid (DomainFunctions.remainder_valid f a ha d z hz)
        (DomainFunctions.remainder_valid f a ha d w hw)))
    (sub_valid (f.eval z hz).property (f.eval w hw).property) (equiv_symm he) hb
  have hr : 2*B*L+(halfDerivativeError.val*H.val+halfDerivativeError.val*H.val)=2*B*L+H.val := by
    unfold halfDerivativeError
    grind only
  rw [hr] at hs
  exact hs

end ComputableAnalysis.ModularForms
