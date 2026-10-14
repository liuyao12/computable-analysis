import ComputableAnalysis.RiemannHilbert.ContourRectangleDomains

/-! Exact affine cancellation and actual derivative remainder estimates. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

def affineMidpointModel (a d z : Scalar) : Scalar :=
  scalarSum a (scalarProduct d z)

def midpointWeightedCycle (right left top bottom x y : Scalar) : Scalar :=
  scalarSum
    (scalarSum (scalarProduct right y) (scalarProduct left (scalarNeg y)))
    (scalarSum (scalarProduct top (scalarNeg x)) (scalarProduct bottom x))

theorem affineMidpointCycle_zero (a d x y : Scalar) :
    (midpointWeightedCycle (affineMidpointModel a d x)
      (affineMidpointModel a d (scalarNeg x))
      (affineMidpointModel a d y) (affineMidpointModel a d (scalarNeg y)) x y).val.Equiv zero := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (midpointWeightedCycle (affineMidpointModel a d x)
      (affineMidpointModel a d (scalarNeg x))
      (affineMidpointModel a d y) (affineMidpointModel a d (scalarNeg y)) x y).property)
    (hright := ofQComplex_valid _)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  change ((A+D*X)*Y+(A+D*(-X))*(-Y))+
    ((A+D*Y)*(-X)+(A+D*(-Y))*X)=0
  grind only

theorem midpointWeightedCycle_difference (r l t b r' l' t' b' x y : Scalar) :
    (sub (midpointWeightedCycle r l t b x y).val
      (midpointWeightedCycle r' l' t' b' x y).val).Equiv
      (midpointWeightedCycle
        ⟨sub r.val r'.val,sub_valid r.property r'.property⟩
        ⟨sub l.val l'.val,sub_valid l.property l'.property⟩
        ⟨sub t.val t'.val,sub_valid t.property t'.property⟩
        ⟨sub b.val b'.val,sub_valid b.property b'.property⟩ x y).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (midpointWeightedCycle r l t b x y).property
      (midpointWeightedCycle r' l' t' b' x y).property)
    (hright := (midpointWeightedCycle
      ⟨sub r.val r'.val,sub_valid r.property r'.property⟩
      ⟨sub l.val l'.val,sub_valid l.property l'.property⟩
      ⟨sub t.val t'.val,sub_valid t.property t'.property⟩
      ⟨sub b.val b'.val,sub_valid b.property b'.property⟩ x y).property)
  let R := ComplexRawQuotient.ofRaw r.val r.property
  let L := ComplexRawQuotient.ofRaw l.val l.property
  let T := ComplexRawQuotient.ofRaw t.val t.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let R' := ComplexRawQuotient.ofRaw r'.val r'.property
  let L' := ComplexRawQuotient.ofRaw l'.val l'.property
  let T' := ComplexRawQuotient.ofRaw t'.val t'.property
  let B' := ComplexRawQuotient.ofRaw b'.val b'.property
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  change ((R*Y+L*(-Y))+(T*(-X)+B*X))-
    ((R'*Y+L'*(-Y))+(T'*(-X)+B'*X))=
      ((R-R')*Y+(L-L')*(-Y))+((T-T')*(-X)+(B-B')*X)
  grind only
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
theorem midpointAffineError_cycle_bound (r l t b A d x y : Scalar) (E H : Rat)
    (hE : 0≤E) (hH : 0≤H)
    (her : Small (sub r.val (affineMidpointModel A d x).val) E)
    (hel : Small (sub l.val (affineMidpointModel A d (scalarNeg x)).val) E)
    (het : Small (sub t.val (affineMidpointModel A d y).val) E)
    (heb : Small (sub b.val (affineMidpointModel A d (scalarNeg y)).val) E)
    (hx : Small x.val H) (hy : Small y.val H) :
    Small (midpointWeightedCycle r l t b x y).val (8*E*H) := by
  let r' := affineMidpointModel A d x
  let l' := affineMidpointModel A d (scalarNeg x)
  let t' := affineMidpointModel A d y
  let b' := affineMidpointModel A d (scalarNeg y)
  have hcycle := midpointWeightedCycle_bound
    ⟨sub r.val r'.val,sub_valid r.property r'.property⟩
    ⟨sub l.val l'.val,sub_valid l.property l'.property⟩
    ⟨sub t.val t'.val,sub_valid t.property t'.property⟩
    ⟨sub b.val b'.val,sub_valid b.property b'.property⟩ x y E H
    hE
    hH her hel het heb hx hy
  have hd := Small.congr
    (midpointWeightedCycle
      ⟨sub r.val r'.val,sub_valid r.property r'.property⟩
      ⟨sub l.val l'.val,sub_valid l.property l'.property⟩
      ⟨sub t.val t'.val,sub_valid t.property t'.property⟩
      ⟨sub b.val b'.val,sub_valid b.property b'.property⟩ x y).property
    (sub_valid (midpointWeightedCycle r l t b x y).property
      (midpointWeightedCycle r' l' t' b' x y).property)
    (equiv_symm (midpointWeightedCycle_difference r l t b r' l' t' b' x y)) hcycle
  have hz := affineMidpointCycle_zero A d x y
  have he : (sub (midpointWeightedCycle r l t b x y).val
      (midpointWeightedCycle r' l' t' b' x y).val).Equiv
      (midpointWeightedCycle r l t b x y).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (midpointWeightedCycle r l t b x y).property
        (midpointWeightedCycle r' l' t' b' x y).property)
      (hright := (midpointWeightedCycle r l t b x y).property)
    have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (midpointWeightedCycle r' l' t' b' x y).property)
      (hright := ofQComplex_valid _) hz
    let C := ComplexRawQuotient.ofRaw (midpointWeightedCycle r l t b x y).val
      (midpointWeightedCycle r l t b x y).property
    let M := ComplexRawQuotient.ofRaw (midpointWeightedCycle r' l' t' b' x y).val
      (midpointWeightedCycle r' l' t' b' x y).property
    change M=0 at hh
    change C-M=C
    rw [hh]
    grind only
  exact Small.congr (sub_valid (midpointWeightedCycle r l t b x y).property
    (midpointWeightedCycle r' l' t' b' x y).property)
    (midpointWeightedCycle r l t b x y).property he hd

end ComputableAnalysis.RiemannHilbert.RectangularContour
