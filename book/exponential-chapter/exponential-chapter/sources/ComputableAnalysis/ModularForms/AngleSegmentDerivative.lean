import ComputableAnalysis.ModularForms.BoundedAngleSegments

/-! Derivative signs at the actual represented segment points. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
namespace BoundedAngle

theorem segment_real_embedding (A B : BoundedAngle) (t : UnitInterval.Point) :
    (RepresentedAffineSegment.point A.scalar B.scalar t).val.Equiv
      (ofRealRaw (segmentReal A B t)) := by
  let z := RepresentedAffineSegment.point A.scalar B.scalar t
  intro n
  apply (compareAt_overlap_iff _ _ n n).2
  have hs := representedAffine_box_sample_mem A.scalar B.scalar t n
  have hl := hs.1.2
  have hu := hs.2.2
  simp only [scalar,ofRealRaw,QComplex.add,QComplex.mul,QComplex.sub,QComplex.neg,
    QComplex.ofRat,Rat.zero_mul,Rat.mul_zero,Rat.zero_add,Rat.add_zero,Rat.neg_zero] at hl hu
  have ho := valid_ordered z.property n
  have hr := ho.1
  change (z.val.compute n).lo.re≤(z.val.compute n).hi.re at hr
  change (z.val.compute n).lo.im≤0 at hl
  change 0≤(z.val.compute n).hi.im at hu
  exact ⟨⟨hr,hl⟩,⟨hr,hu⟩⟩

theorem segment_scalar_agreement (A B : BoundedAngle) (t : UnitInterval.Point) :
    (segment A B t).scalar.val.Equiv
      (RepresentedAffineSegment.point A.scalar B.scalar t).val :=
  equiv_trans (segment A B t).scalar.property
    (ofRealRaw_valid _ (segmentReal_valid A B t))
    (RepresentedAffineSegment.point A.scalar B.scalar t).property
    (ofRealRaw_equiv_of_equiv (segmentReboxed_valid A B t) (segmentReal_valid A B t)
      (segmentReboxed_equiv A B t)) (equiv_symm (segment_real_embedding A B t))

theorem actual_segment_rotation_positive (A B : BoundedAngle) (t : UnitInterval.Point) :
    InUpperHalfPlane (angleRotationMap.eval
      (RepresentedAffineSegment.point A.scalar B.scalar t) ⟨trivial,trivial⟩).val := by
  let C := segment A B t
  let x := RepresentedAffineSegment.point A.scalar B.scalar t
  have hc := angleRotationMap.eval_congr C.scalar x ⟨trivial,trivial⟩ ⟨trivial,trivial⟩
    (segment_scalar_agreement A B t)
  let D := C.rotationInput
  have he := angleRotationMap_real_input_agreement D
  have hs := ofRealRaw_equiv_of_equiv D.valid C.valid C.rotationInput_agreement
  have ha := angleRotationMap.eval_congr
    ⟨ofRealRaw D.raw,ofRealRaw_valid _ D.valid⟩ C.scalar
    ⟨trivial,trivial⟩ ⟨trivial,trivial⟩ hs
  have hp := (upperHalfPlane_congr
    (angleRotationMap.eval ⟨ofRealRaw D.raw,ofRealRaw_valid _ D.valid⟩ ⟨trivial,trivial⟩).property
    (RotationLift.HalfPiInput.rotation_valid D) he).mpr (rotationQuarter_represented_positive D)
  have hC := (upperHalfPlane_congr
    (angleRotationMap.eval ⟨ofRealRaw D.raw,ofRealRaw_valid _ D.valid⟩ ⟨trivial,trivial⟩).property
    (angleRotationMap.eval C.scalar ⟨trivial,trivial⟩).property ha).mp hp
  exact (upperHalfPlane_congr (angleRotationMap.eval C.scalar ⟨trivial,trivial⟩).property
    (angleRotationMap.eval x ⟨trivial,trivial⟩).property hc).mp hC

theorem actual_segment_derivative_negative (A B : BoundedAngle) (t : UnitInterval.Point) :
    (angleRotationMap_holomorphic.derivative
      (RepresentedAffineSegment.point A.scalar B.scalar t) ⟨trivial,trivial⟩).val.realPart.Neg := by
  let x := RepresentedAffineSegment.point A.scalar B.scalar t
  let e := angleRotationMap.eval x ⟨trivial,trivial⟩
  let d := angleRotationMap_holomorphic.derivative x ⟨trivial,trivial⟩
  have hp := imaginary_unit_mul_negative_real e (actual_segment_rotation_positive A B t)
  have hd := angleRotationMap_differential_identity x ⟨trivial,trivial⟩
  have hn := positive_of_equiv
    (RealRaw.neg_valid (realPart_valid (mul_valid latticeImaginaryUnit.property e.property)))
    (RealRaw.neg_valid (realPart_valid d.property))
    (RealRaw.neg_equiv (realPart_equiv (equiv_symm hd))) hp
  obtain ⟨N,hN⟩ := hn
  refine ⟨N,?_⟩
  change 0 < -(d.val.compute N).hi.re at hN
  change (d.val.compute N).hi.re < 0
  grind only

end BoundedAngle
end ComputableAnalysis.ModularForms
