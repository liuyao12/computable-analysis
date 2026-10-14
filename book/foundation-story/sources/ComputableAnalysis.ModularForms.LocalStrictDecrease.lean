import ComputableAnalysis.ModularForms.RepresentedScalarValue
import ComputableAnalysis.ModularForms.PairedDenominatorAgreement
import ComputableAnalysis.ModularForms.NegativeIncrementRemainder

/-! Actual derivative estimates imply strict decrease for short positive
real rational displacements. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem local_strict_decrease (f : DomainFunctions.Map) (hf : DomainFunctions.Holomorphic f)
    (a : Scalar) (ha : f.domain a)
    (hd : (hf.derivative a ha).val.realPart.Neg) :
    ∃ D : QPos, ∀ (h : QPos) (z : Scalar) (hz : f.domain z),
      h.val≤D.val → (sub z.val a.val).Equiv (ofQComplex ⟨h.val,0⟩) →
      (sub (f.eval z hz).val (f.eval a ha).val).realPart.Neg := by
  let d := hf.derivative a ha
  obtain ⟨N,hN⟩ := hd
  change (d.val.compute N).hi.re<0 at hN
  let eps : QPos := ⟨-(d.val.compute N).hi.re/2,by
    have hn : 0< -(d.val.compute N).hi.re := by grind only
    rw [Rat.div_def]
    exact Rat.mul_pos hn (by decide +kernel)⟩
  refine ⟨(hf.atPoint a ha).delta eps,?_⟩
  intro h z hz hh hza
  have hs : Small (ofQComplex ⟨h.val,0⟩) h.val := by
    refine ⟨?_,?_,?_,?_⟩ <;> intro n m
    all_goals simp only [ofQComplex,realPart,imagPart,RealRaw.ofRat]
    all_goals have hp := h.property
    all_goals grind only
  have hsza := Small.congr (ofQComplex_valid _) (sub_valid z.property a.property)
    (equiv_symm hza) hs
  have hr := (hf.atPoint a ha).estimate eps h z hz hh hsza
  let e : Scalar := ⟨DomainFunctions.remainder f a ha d z hz,
    DomainFunctions.remainder_valid f a ha d z hz⟩
  let l : Scalar := ⟨scaleRat h.val d.val,scaleRat_valid d.property⟩
  let v : Scalar := ⟨sub (f.eval z hz).val (f.eval a ha).val,
    sub_valid (f.eval z hz).property (f.eval a ha).property⟩
  have hl : (l.val.compute N).hi.re<0 := by
    change (QBox.scaleRat h.val (d.val.compute N)).hi.re<0
    simp only [QBox.scaleRat,if_pos (Rat.le_of_lt h.property)]
    have hp := Rat.mul_pos h.property (show 0< -(d.val.compute N).hi.re by grind only)
    grind only
  have he : Small e.val (-(l.val.compute N).hi.re/2) := by
    have hc : eps.val*h.val= -(l.val.compute N).hi.re/2 := by
      change (-(d.val.compute N).hi.re/2)*h.val=
        -(QBox.scaleRat h.val (d.val.compute N)).hi.re/2
      simp only [QBox.scaleRat,if_pos (Rat.le_of_lt h.property)]
      grind only
    rw [hc] at hr
    exact hr
  have heq : (add l.val e.val).Equiv v.val := by
    have hb := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := sub_valid z.property a.property) (hright := ofQComplex_valid _) hza
    have hc := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := scaleRat_valid (r := h.val) (ofQComplex_valid _))
      (hright := ofQComplex_valid _) (rationalScalarOne_equiv h.val)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid l.property e.property) (hright := v.property)
    let D := gridScalarValue d
    let Z := gridScalarValue z
    let A := gridScalarValue a
    let V := gridScalarValue v
    change Z-A=ComplexRawQuotient.ofQComplex ⟨h.val,0⟩ at hb
    change ComplexRawQuotient.scaleRat h.val 1=ComplexRawQuotient.ofQComplex ⟨h.val,0⟩ at hc
    change ComplexRawQuotient.scaleRat h.val D+(V-D*(Z-A))=V
    rw [hb,←hc,ComplexRawQuotient.mul_scaleRat]
    grind only
  exact negative_real_add_small_equiv l e v N hl he heq

theorem angle_segment_local_strict_decrease (A B : BoundedAngle) (t : UnitInterval.Point) :
    ∃ D : QPos, ∀ (h : QPos) (z : Scalar), h.val≤D.val →
      (sub z.val (RepresentedAffineSegment.point A.scalar B.scalar t).val).Equiv
        (ofQComplex ⟨h.val,0⟩) →
      (sub (angleRotationMap.eval z ⟨trivial,trivial⟩).val
        (angleRotationMap.eval (RepresentedAffineSegment.point A.scalar B.scalar t)
          ⟨trivial,trivial⟩).val).realPart.Neg := by
  obtain ⟨D,hD⟩ := local_strict_decrease angleRotationMap angleRotationMap_holomorphic
    (RepresentedAffineSegment.point A.scalar B.scalar t) ⟨trivial,trivial⟩
    (BoundedAngle.actual_segment_derivative_negative A B t)
  exact ⟨D,fun h z hh he => hD h z ⟨trivial,trivial⟩ hh he⟩

end ComputableAnalysis.ModularForms
