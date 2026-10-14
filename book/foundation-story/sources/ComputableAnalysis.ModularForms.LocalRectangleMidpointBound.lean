import ComputableAnalysis.ModularForms.LocalAffineModelError

/-! Local rectangle midpoint estimates derived from actual differentiation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem translatedAffineModel_error (f : DomainFunctions.Map) (a d w : Scalar)
    (ha : f.domain a) (hf : HasDerivativeAt f a ha d)
    (eps H : QPos) (hH : H.val≤(hf.delta eps).val)
    (hw : f.domain (Centered.translate a w)) (hnear : Small w.val H.val) :
    Small (sub (f.eval (Centered.translate a w) hw).val
      (affineMidpointModel (f.eval a ha) d w).val) (eps.val*H.val) := by
  have hn := Small.congr w.property (Centered.offset a (Centered.translate a w)).property
    (equiv_symm (Centered.offset_translate a w)) hnear
  have hb := localAffineModel_error_bound f a d ha hf eps H hH
    (Centered.translate a w) hw hn
  have he := add_equiv (equiv_refl _ (f.eval a ha).property)
    (mul_equiv d.property d.property (Centered.offset a (Centered.translate a w)).property
      w.property (equiv_refl _ d.property) (Centered.offset_translate a w))
  exact Small.congr
    (sub_valid (f.eval (Centered.translate a w) hw).property
      (affineMidpointModel (f.eval a ha) d (Centered.offset a (Centered.translate a w))).property)
    (sub_valid (f.eval (Centered.translate a w) hw).property
      (affineMidpointModel (f.eval a ha) d w).property)
    (FunctionTheory.sub_congr (equiv_refl _ (f.eval (Centered.translate a w) hw).property) he) hb

theorem localRectangleMidpoint_bound (f : DomainFunctions.Map) (a d x y : Scalar)
    (ha : f.domain a) (hf : HasDerivativeAt f a ha d)
    (eps H : QPos) (hH : H.val≤(hf.delta eps).val)
    (hr : f.domain (Centered.translate a x))
    (hl : f.domain (Centered.translate a (scalarNeg x)))
    (ht : f.domain (Centered.translate a y))
    (hb : f.domain (Centered.translate a (scalarNeg y)))
    (hx : Small x.val H.val) (hy : Small y.val H.val) :
    Small (midpointWeightedCycle
      (f.eval (Centered.translate a x) hr)
      (f.eval (Centered.translate a (scalarNeg x)) hl)
      (f.eval (Centered.translate a y) ht)
      (f.eval (Centered.translate a (scalarNeg y)) hb) x y).val
      (8*(eps.val*H.val)*H.val) := by
  let A := f.eval a ha
  let r := f.eval (Centered.translate a x) hr
  let l := f.eval (Centered.translate a (scalarNeg x)) hl
  let t := f.eval (Centered.translate a y) ht
  let b := f.eval (Centered.translate a (scalarNeg y)) hb
  let r' := affineMidpointModel A d x
  let l' := affineMidpointModel A d (scalarNeg x)
  let t' := affineMidpointModel A d y
  let b' := affineMidpointModel A d (scalarNeg y)
  have her := translatedAffineModel_error f a d x ha hf eps H hH hr hx
  have hel := translatedAffineModel_error f a d (scalarNeg x) ha hf eps H hH hl (SeriesLimitLaws.small_neg hx)
  have het := translatedAffineModel_error f a d y ha hf eps H hH ht hy
  have heb := translatedAffineModel_error f a d (scalarNeg y) ha hf eps H hH hb (SeriesLimitLaws.small_neg hy)
  have hcycle := midpointWeightedCycle_bound
    ⟨sub r.val r'.val,sub_valid r.property r'.property⟩
    ⟨sub l.val l'.val,sub_valid l.property l'.property⟩
    ⟨sub t.val t'.val,sub_valid t.property t'.property⟩
    ⟨sub b.val b'.val,sub_valid b.property b'.property⟩ x y (eps.val*H.val) H.val
    (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property))
    (Rat.le_of_lt H.property) her hel het heb hx hy
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

end ComputableAnalysis.ModularForms
