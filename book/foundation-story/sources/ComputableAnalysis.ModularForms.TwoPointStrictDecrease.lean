import ComputableAnalysis.ModularForms.StrictDecreaseChain

/-! Two-point strict comparisons from a common represented derivative center. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem two_point_strict_decrease (f : DomainFunctions.Map) (hf : DomainFunctions.Holomorphic f)
    (a : Scalar) (ha : f.domain a)
    (hd : (hf.derivative a ha).val.realPart.Neg) :
    ∃ D : QPos, ∀ (h : QPos) (z w : Scalar) (hz : f.domain z) (hw : f.domain w),
      h.val≤D.val → Small (sub z.val a.val) h.val → Small (sub w.val a.val) h.val →
      (sub z.val w.val).Equiv (ofQComplex ⟨h.val,0⟩) →
      (sub (f.eval z hz).val (f.eval w hw).val).realPart.Neg := by
  let d := hf.derivative a ha
  obtain ⟨N,hN⟩ := hd
  change (d.val.compute N).hi.re<0 at hN
  let eps : QPos := ⟨-(d.val.compute N).hi.re/4,by
    have hn : 0< -(d.val.compute N).hi.re := by grind only
    rw [Rat.div_def]
    exact Rat.mul_pos hn (by decide +kernel)⟩
  refine ⟨(hf.atPoint a ha).delta eps,?_⟩
  intro h z w hz hw hh hza hwa hzw
  have hrz := (hf.atPoint a ha).estimate eps h z hz hh hza
  have hrw := (hf.atPoint a ha).estimate eps h w hw hh hwa
  let rz : Scalar := ⟨DomainFunctions.remainder f a ha d z hz,
    DomainFunctions.remainder_valid f a ha d z hz⟩
  let rw : Scalar := ⟨DomainFunctions.remainder f a ha d w hw,
    DomainFunctions.remainder_valid f a ha d w hw⟩
  let e : Scalar := ⟨sub rz.val rw.val,sub_valid rz.property rw.property⟩
  have hr := LocalODE.small_add hrz (SeriesLimitLaws.small_neg hrw)
  let l : Scalar := ⟨scaleRat h.val d.val,scaleRat_valid d.property⟩
  let v : Scalar := ⟨sub (f.eval z hz).val (f.eval w hw).val,
    sub_valid (f.eval z hz).property (f.eval w hw).property⟩
  have hl : (l.val.compute N).hi.re<0 := by
    change (QBox.scaleRat h.val (d.val.compute N)).hi.re<0
    simp only [QBox.scaleRat,if_pos (Rat.le_of_lt h.property)]
    have hp := Rat.mul_pos h.property (show 0< -(d.val.compute N).hi.re by grind only)
    grind only
  have he : Small e.val (-(l.val.compute N).hi.re/2) := by
    have hc : eps.val*h.val+eps.val*h.val= -(l.val.compute N).hi.re/2 := by
      change (-(d.val.compute N).hi.re/4)*h.val+(-(d.val.compute N).hi.re/4)*h.val=
        -(QBox.scaleRat h.val (d.val.compute N)).hi.re/2
      simp only [QBox.scaleRat,if_pos (Rat.le_of_lt h.property)]
      grind only
    rw [hc] at hr
    exact hr
  have heq : (add l.val e.val).Equiv v.val := by
    have hb := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := sub_valid z.property w.property) (hright := ofQComplex_valid _) hzw
    have hc := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := scaleRat_valid (r := h.val) (ofQComplex_valid _))
      (hright := ofQComplex_valid _) (rationalScalarOne_equiv h.val)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid l.property e.property) (hright := v.property)
    let D := gridScalarValue d
    let Z := gridScalarValue z
    let W := gridScalarValue w
    let A := gridScalarValue a
    let FZ := gridScalarValue (f.eval z hz)
    let FW := gridScalarValue (f.eval w hw)
    let FA := gridScalarValue (f.eval a ha)
    let V := gridScalarValue v
    change Z-W=ComplexRawQuotient.ofQComplex ⟨h.val,0⟩ at hb
    change ComplexRawQuotient.scaleRat h.val 1=ComplexRawQuotient.ofQComplex ⟨h.val,0⟩ at hc
    have hlin : D*(Z-W)=ComplexRawQuotient.scaleRat h.val D := by
      rw [hb,←hc,ComplexRawQuotient.mul_scaleRat]
      grind only
    change ComplexRawQuotient.scaleRat h.val D+
      ((FZ-FA-D*(Z-A))-(FW-FA-D*(W-A)))=FZ-FW
    rw [←hlin]
    grind only
  exact negative_real_add_small_equiv l e v N hl he heq

theorem angle_segment_two_point_strict_decrease (A B : BoundedAngle) (t : UnitInterval.Point) :
    ∃ D : QPos, ∀ (h : QPos) (z w : Scalar), h.val≤D.val →
      Small (sub z.val (RepresentedAffineSegment.point A.scalar B.scalar t).val) h.val →
      Small (sub w.val (RepresentedAffineSegment.point A.scalar B.scalar t).val) h.val →
      (sub z.val w.val).Equiv (ofQComplex ⟨h.val,0⟩) →
      (sub (angleRotationMap.eval z ⟨trivial,trivial⟩).val
        (angleRotationMap.eval w ⟨trivial,trivial⟩).val).realPart.Neg := by
  obtain ⟨D,hD⟩ := two_point_strict_decrease angleRotationMap angleRotationMap_holomorphic
    (RepresentedAffineSegment.point A.scalar B.scalar t) ⟨trivial,trivial⟩
    (BoundedAngle.actual_segment_derivative_negative A B t)
  exact ⟨D,fun h z w hh hz hw he => hD h z w ⟨trivial,trivial⟩ ⟨trivial,trivial⟩ hh hz hw he⟩

end ComputableAnalysis.ModularForms
