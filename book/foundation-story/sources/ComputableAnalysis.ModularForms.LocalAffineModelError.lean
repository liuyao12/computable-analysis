import ComputableAnalysis.ModularForms.AffineMidpointCycleCancellation

/-! Actual derivative remainders are exactly the local affine-model errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem localAffineModel_error_equiv (f : DomainFunctions.Map) (a d z : Scalar)
    (ha : f.domain a) (hz : f.domain z) :
    (sub (f.eval z hz).val (affineMidpointModel (f.eval a ha) d (Centered.offset a z)).val).Equiv
      (remainder f a ha d z hz) := by
  have hr := difference_remainder f a ha d z hz
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := sub_valid (f.eval z hz).property (f.eval a ha).property)
    (hright := add_valid (mul_valid d.property (sub_valid z.property a.property))
      (remainder_valid f a ha d z hz)) hr
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (f.eval z hz).property
      (affineMidpointModel (f.eval a ha) d (Centered.offset a z)).property)
    (hright := remainder_valid f a ha d z hz)
  let F := ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property
  let A := ComplexRawQuotient.ofRaw (f.eval a ha).val (f.eval a ha).property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let C := ComplexRawQuotient.ofRaw a.val a.property
  let E := ComplexRawQuotient.ofRaw (remainder f a ha d z hz) (remainder_valid f a ha d z hz)
  change F-A=D*(Z-C)+E at hh
  change F-(A+D*(Z-C))=E
  grind only

theorem localAffineModel_error_bound (f : DomainFunctions.Map) (a d : Scalar)
    (ha : f.domain a) (hf : HasDerivativeAt f a ha d)
    (eps H : QPos) (hH : H.val≤(hf.delta eps).val)
    (z : Scalar) (hz : f.domain z) (hnear : Small (sub z.val a.val) H.val) :
    Small (sub (f.eval z hz).val
      (affineMidpointModel (f.eval a ha) d (Centered.offset a z)).val) (eps.val*H.val) :=
  Small.congr (remainder_valid f a ha d z hz)
    (sub_valid (f.eval z hz).property
      (affineMidpointModel (f.eval a ha) d (Centered.offset a z)).property)
    (equiv_symm (localAffineModel_error_equiv f a d z ha hz))
    (hf.estimate eps H z hz hH hnear)

theorem midpointWeightedCycle_bound (r l t b x y : Scalar) (E H : Rat)
    (hE : 0≤E) (hH : 0≤H)
    (hr : Small r.val E) (hl : Small l.val E) (ht : Small t.val E) (hb : Small b.val E)
    (hx : Small x.val H) (hy : Small y.val H) :
    Small (midpointWeightedCycle r l t b x y).val (8*E*H) := by
  have h1 := Small.mul r.property y.property hE hH hr hy
  have h2 := Small.mul l.property (scalarNeg y).property hE hH hl (SeriesLimitLaws.small_neg hy)
  have h3 := Small.mul t.property (scalarNeg x).property hE hH ht (SeriesLimitLaws.small_neg hx)
  have h4 := Small.mul b.property x.property hE hH hb hx
  have hs := LocalODE.small_add (LocalODE.small_add h1 h2) (LocalODE.small_add h3 h4)
  have he : (2*E*H+2*E*H)+(2*E*H+2*E*H)=8*E*H := by grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.ModularForms
