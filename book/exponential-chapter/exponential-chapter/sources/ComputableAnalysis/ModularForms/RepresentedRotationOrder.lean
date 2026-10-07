import ComputableAnalysis.ModularForms.OrderApproximationLimit

/-! Exact rotation order for arbitrary represented bounded angles. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem boundedAngle_rational_sample_near (A : BoundedAngle) (N : Nat) (r : Rat)
    (hr : (A.raw.compute N).lo≤r ∧ r≤(A.raw.compute N).hi)
    (D : QPos) (hw : (A.raw.compute N).width≤D.val) :
    Small (sub (rationalAngleScalar r).val A.scalar.val) D.val := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · have ho := (RealRaw.compareAt_overlap_iff _ _ N m).1
      (RealRaw.allStagesOverlap_refl A.raw A.valid N m)
    have h := ho.2
    change -D.val≤r+ -(A.raw.compute m).lo
    change (A.raw.compute m).lo≤(A.raw.compute N).hi at h
    change (A.raw.compute N).hi-(A.raw.compute N).lo≤D.val at hw
    grind only
  · have ho := (RealRaw.compareAt_overlap_iff _ _ N n).1
      (RealRaw.allStagesOverlap_refl A.raw A.valid N n)
    have h := ho.1
    change r+ -(A.raw.compute n).hi≤D.val
    change (A.raw.compute N).lo≤(A.raw.compute n).hi at h
    change (A.raw.compute N).hi-(A.raw.compute N).lo≤D.val at hw
    grind only
  · change -D.val≤(0:Rat)+ -0
    have hp := D.property
    grind only
  · change (0:Rat)+ -0≤D.val
    have hp := D.property
    grind only

theorem small_reverse_difference (x y : Scalar) (E : Rat)
    (h : Small (sub x.val y.val) E) : Small (sub y.val x.val) E := by
  have he : (neg (sub x.val y.val)).Equiv (sub y.val x.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (sub_valid x.property y.property))
      (hright := sub_valid y.property x.property)
    change -(gridScalarValue x-gridScalarValue y)=gridScalarValue y-gridScalarValue x
    grind only
  exact Small.congr (neg_valid (sub_valid x.property y.property))
    (sub_valid y.property x.property) he (SeriesLimitLaws.small_neg h)

theorem represented_rotation_order (A B : BoundedAngle) (hab : A.raw.Le B.raw) :
    (angleRotationMap.eval B.scalar ⟨trivial,trivial⟩).val.realPart.Le
      (angleRotationMap.eval A.scalar ⟨trivial,trivial⟩).val.realPart := by
  let x := angleRotationMap.eval A.scalar ⟨trivial,trivial⟩
  let y := angleRotationMap.eval B.scalar ⟨trivial,trivial⟩
  apply real_order_of_accurate_approximations x y
  intro eps
  let ca := (angleRotationMap_holomorphic.atPoint A.scalar ⟨trivial,trivial⟩).continuousAt
  let cb := (angleRotationMap_holomorphic.atPoint B.scalar ⟨trivial,trivial⟩).continuousAt
  let Na := A.widthStage (ca.delta eps)
  let Nb := B.widthStage (cb.delta eps)
  let u := (A.raw.compute Na).lo
  let v := (B.raw.compute Nb).hi
  have hoa := RealRaw.interval_order_of_valid A.raw A.valid Na
  have hob := RealRaw.interval_order_of_valid B.raw B.valid Nb
  have hnearA := boundedAngle_rational_sample_near A Na u ⟨Rat.le_refl,hoa⟩
    (ca.delta eps) (A.widthStage_spec (ca.delta eps))
  have hnearB := boundedAngle_rational_sample_near B Nb v ⟨hob,Rat.le_refl⟩
    (cb.delta eps) (B.widthStage_spec (cb.delta eps))
  let a := angleRotationMap.eval (rationalAngleScalar u) ⟨trivial,trivial⟩
  let b := angleRotationMap.eval (rationalAngleScalar v) ⟨trivial,trivial⟩
  have hA := ca.estimate eps (rationalAngleScalar u) ⟨trivial,trivial⟩ hnearA
  have hB := cb.estimate eps (rationalAngleScalar v) ⟨trivial,trivial⟩ hnearB
  have huv : u≤v := hab Na Nb
  have hu : 1≤u := (A.bounds Na).1
  have hv : v≤2 := (B.bounds Nb).2
  exact ⟨a,b,rational_rotation_order_of_le u v hu hv huv,
    small_reverse_difference a x eps.val hA,small_reverse_difference b y eps.val hB⟩

end ComputableAnalysis.ModularForms
