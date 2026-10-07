import ComputableAnalysis.ModularForms.PairedRiccatiLinearizedVariation
import ComputableAnalysis.ModularForms.LocalRectangleMidpointBound

/-! Width-scaled actual rectangle estimates from derivative continuity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem pairedRiccati_translated_neighborhood_model_error (a c w : Scalar)
    (eps H : QPos)
    (hc : Small (Centered.offset a c).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val)
    (hq : Small (Centered.offset a (Centered.translate c w)).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val)
    (hnear : Small w.val H.val) :
    Small (sub (pairedEntireRiccatiMap.eval (Centered.translate c w) trivial).val
      (affineMidpointModel (pairedEntireRiccatiMap.eval c trivial)
        (pairedEntireRiccatiMap_holomorphic.derivative a trivial) w).val)
      (4*eps.val*H.val) := by
  let f := pairedEntireRiccatiMap
  let d := pairedEntireRiccatiMap_holomorphic.derivative a trivial
  have hn := Small.congr w.property (Centered.offset c (Centered.translate c w)).property
    (equiv_symm (Centered.offset_translate c w)) hnear
  have hr := pairedRiccati_neighborhood_linearization a c (Centered.translate c w) H eps hn hc hq
  have hb := Small.congr (remainder_valid f c trivial d (Centered.translate c w) trivial)
    (sub_valid (f.eval (Centered.translate c w) trivial).property
      (affineMidpointModel (f.eval c trivial) d (Centered.offset c (Centered.translate c w))).property)
    (equiv_symm (localAffineModel_error_equiv f c d (Centered.translate c w) trivial trivial)) hr
  have he := add_equiv (equiv_refl _ (f.eval c trivial).property)
    (mul_equiv d.property d.property (Centered.offset c (Centered.translate c w)).property
      w.property (equiv_refl _ d.property) (Centered.offset_translate c w))
  exact Small.congr
    (sub_valid (f.eval (Centered.translate c w) trivial).property
      (affineMidpointModel (f.eval c trivial) d (Centered.offset c (Centered.translate c w))).property)
    (sub_valid (f.eval (Centered.translate c w) trivial).property
      (affineMidpointModel (f.eval c trivial) d w).property)
    (FunctionTheory.sub_congr (equiv_refl _ (f.eval (Centered.translate c w) trivial).property) he) hb

theorem pairedRiccati_rectangle_neighborhood_bound (a c x y : Scalar) (eps H : QPos)
    (hc : Small (Centered.offset a c).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val)
    (hr : Small (Centered.offset a (Centered.translate c x)).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val)
    (hl : Small (Centered.offset a (Centered.translate c (scalarNeg x))).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val)
    (ht : Small (Centered.offset a (Centered.translate c y)).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val)
    (hb : Small (Centered.offset a (Centered.translate c (scalarNeg y))).val
      (pairedEntireRiccatiMap_holomorphic.continuousDerivative.delta a trivial eps).val)
    (hx : Small x.val H.val) (hy : Small y.val H.val) :
    Small (midpointWeightedCycle
      (pairedEntireRiccatiMap.eval (Centered.translate c x) trivial)
      (pairedEntireRiccatiMap.eval (Centered.translate c (scalarNeg x)) trivial)
      (pairedEntireRiccatiMap.eval (Centered.translate c y) trivial)
      (pairedEntireRiccatiMap.eval (Centered.translate c (scalarNeg y)) trivial) x y).val
      (8*(4*eps.val*H.val)*H.val) := by
  let f := pairedEntireRiccatiMap
  let d := pairedEntireRiccatiMap_holomorphic.derivative a trivial
  let A := f.eval c trivial
  let r := f.eval (Centered.translate c x) trivial
  let l := f.eval (Centered.translate c (scalarNeg x)) trivial
  let t := f.eval (Centered.translate c y) trivial
  let b := f.eval (Centered.translate c (scalarNeg y)) trivial
  let r' := affineMidpointModel A d x
  let l' := affineMidpointModel A d (scalarNeg x)
  let t' := affineMidpointModel A d y
  let b' := affineMidpointModel A d (scalarNeg y)
  have her := pairedRiccati_translated_neighborhood_model_error a c x eps H hc hr hx
  have hel := pairedRiccati_translated_neighborhood_model_error a c (scalarNeg x) eps H hc hl
    (SeriesLimitLaws.small_neg hx)
  have het := pairedRiccati_translated_neighborhood_model_error a c y eps H hc ht hy
  have heb := pairedRiccati_translated_neighborhood_model_error a c (scalarNeg y) eps H hc hb
    (SeriesLimitLaws.small_neg hy)
  have hcycle := midpointWeightedCycle_bound
    ⟨sub r.val r'.val,sub_valid r.property r'.property⟩
    ⟨sub l.val l'.val,sub_valid l.property l'.property⟩
    ⟨sub t.val t'.val,sub_valid t.property t'.property⟩
    ⟨sub b.val b'.val,sub_valid b.property b'.property⟩ x y (4*eps.val*H.val) H.val
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property)) (Rat.le_of_lt H.property))
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
