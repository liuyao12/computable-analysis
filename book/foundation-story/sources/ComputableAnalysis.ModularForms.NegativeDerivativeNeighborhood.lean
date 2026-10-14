import ComputableAnalysis.ModularForms.LocalStrictDecrease

/-! A strictly negative derivative persists on a proved neighborhood. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem negative_derivative_neighborhood (f : DomainFunctions.Map)
    (hf : DomainFunctions.Holomorphic f) (a : Scalar) (ha : f.domain a)
    (hd : (hf.derivative a ha).val.realPart.Neg) :
    ∃ R : QPos, ∀ (z : Scalar) (hz : f.domain z),
      Small (sub z.val a.val) R.val → (hf.derivative z hz).val.realPart.Neg := by
  let d := hf.derivative a ha
  obtain ⟨N,hN⟩ := hd
  change (d.val.compute N).hi.re<0 at hN
  let eps : QPos := ⟨-(d.val.compute N).hi.re/2,by
    have hp : 0< -(d.val.compute N).hi.re := by grind only
    rw [Rat.div_def]
    exact Rat.mul_pos hp (by decide +kernel)⟩
  refine ⟨hf.continuousDerivative.delta a ha eps,?_⟩
  intro z hz hza
  let v := hf.derivative z hz
  let e : Scalar := ⟨sub v.val d.val,sub_valid v.property d.property⟩
  have he := hf.continuousDerivative.estimate a ha eps z hz hza
  have hv : (add d.val e.val).Equiv v.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid d.property e.property) (hright := v.property)
    change gridScalarValue d+(gridScalarValue v-gridScalarValue d)=gridScalarValue v
    grind only
  exact negative_real_add_small_equiv d e v N hN he hv

theorem angle_segment_negative_derivative_neighborhood (A B : BoundedAngle)
    (t : UnitInterval.Point) :
    ∃ R : QPos, ∀ z : Scalar,
      Small (sub z.val (RepresentedAffineSegment.point A.scalar B.scalar t).val) R.val →
      (angleRotationMap_holomorphic.derivative z ⟨trivial,trivial⟩).val.realPart.Neg := by
  obtain ⟨R,hR⟩ := negative_derivative_neighborhood angleRotationMap angleRotationMap_holomorphic
    (RepresentedAffineSegment.point A.scalar B.scalar t) ⟨trivial,trivial⟩
    (BoundedAngle.actual_segment_derivative_negative A B t)
  exact ⟨R,fun z hz => hR z ⟨trivial,trivial⟩ hz⟩

end ComputableAnalysis.ModularForms
