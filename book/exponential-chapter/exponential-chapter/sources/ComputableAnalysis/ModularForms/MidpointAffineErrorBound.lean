import ComputableAnalysis.ModularForms.LocalRectangleMidpointBound

/-! Actual affine-model sample errors imply a weighted cycle bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

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

end ComputableAnalysis.ModularForms
