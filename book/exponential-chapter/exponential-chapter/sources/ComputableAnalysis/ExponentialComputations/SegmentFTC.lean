import ComputableAnalysis.ExponentialComputations.SegmentEstimates
import ComputableAnalysis.ExponentialComputations.RectangleValue

/-! The actual reciprocal integrand on the positive segment has the global
logarithm as its endpoint function, by finite remainder bounds. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions ModularForms
set_option maxHeartbeats 1000000

theorem real_embedding_sub (x y : RealInput) :
    (sub (realAxis x).val (realAxis y).val).Equiv
      (ofRealRaw (RealRaw.sub x.val y.val)) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid (RealRaw.sub x.val y.val) (RealRaw.sub_valid x.property y.property) n
  simp only [realAxis,ofRealRaw,sub,add,neg,QBox.add,QBox.neg,QComplex.add,QComplex.neg,
    RealRaw.sub,RealRaw.subCompute,Rat.neg_zero,Rat.zero_add,Rat.sub_eq_add_neg] at ho ⊢
  constructor <;> constructor <;> first | exact ho | exact Rat.le_refl

def segmentIntegrand (x : PositiveInput) : FunctionOnInterval :=
  FunctionOnInterval.ofStable
    {definedAt := fun t => 0≤t ∧ t≤1
     compute := fun t n => if ht : 0≤t ∧ t≤1 then (segmentIntegrandValue x ⟨t,ht⟩).val.compute n else {lo := 0,hi := 0}
     rate := fun _ => .unknown}
    0 1 (fun _ ht => ht) (by
      intro t ht
      simp only [dif_pos ht]
      exact (segmentIntegrandValue x ⟨t,ht⟩).property)

theorem segmentIntegrand_compute (x : PositiveInput) (t : RationalUnit) (n : Nat) :
    (segmentIntegrand x).compute t.val t.property n = (segmentIntegrandValue x t).val.compute n := by
  change (if ht : 0≤t.val ∧ t.val≤1 then (segmentIntegrandValue x ⟨t.val,ht⟩).val.compute n
    else {lo := 0,hi := 0}) = _
  rw [dif_pos t.property]

theorem segmentVariation_nonnegative (x : PositiveInput) : 0≤segmentVariation x := by
  dsimp [segmentVariation]
  exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (Rat.le_of_lt (segmentBound_pos x))))
    (Rat.pow_nonneg (by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr (segmentLower x).property)))

theorem segmentIntegrand_lipschitz (x : PositiveInput) (u v : Rat)
    (hu : inDomainInterval (segmentIntegrand x).lower (segmentIntegrand x).upper u)
    (hv : inDomainInterval (segmentIntegrand x).lower (segmentIntegrand x).upper v) :
    Small (ofRealRaw (RealRaw.sub
      {compute := (segmentIntegrand x).compute u hu} {compute := (segmentIntegrand x).compute v hv}))
      (segmentVariation x*qabs (u-v)) := by
  have h := segmentIntegrand_variation x ⟨v,hv⟩ ⟨u,hu⟩
  have hh := Small.congr
    (sub_valid (realAxis (segmentIntegrandValue x ⟨u,hu⟩)).property (realAxis (segmentIntegrandValue x ⟨v,hv⟩)).property)
    (ofRealRaw_valid _ (RealRaw.sub_valid (segmentIntegrandValue x ⟨u,hu⟩).property (segmentIntegrandValue x ⟨v,hv⟩).property))
    (real_embedding_sub _ _) h
  have hcompute (t : Rat) (ht : inDomainInterval (segmentIntegrand x).lower (segmentIntegrand x).upper t) :
      (segmentIntegrand x).compute t ht = (segmentIntegrandValue x ⟨t,ht⟩).val.compute := by
    funext n
    exact segmentIntegrand_compute x ⟨t,ht⟩ n
  change Small (ofRealRaw (RealRaw.sub (segmentIntegrandValue x ⟨u,hu⟩).val
    (segmentIntegrandValue x ⟨v,hv⟩).val)) _ at hh
  simpa only [Small,RealRaw.Le,ofRealRaw,realPart,imagPart,RealRaw.sub,RealRaw.subCompute,
    hcompute u hu,hcompute v hv] using hh

def segmentRemainderConstant (x : PositiveInput) : Rat :=
  64*(segmentBound x)^2*(1/(segmentLower x).val)^2

def segmentMesh (x : PositiveInput) : QPos :=
  ⟨(segmentLower x).val/(256*segmentBound x),by
    rw [Rat.div_def]
    exact Rat.mul_pos (segmentLower x).property
      (Rat.inv_pos.mpr (Rat.mul_pos (by decide +kernel) (segmentBound_pos x)))⟩

/-- The linear term in the local logarithm is exactly the requested
reciprocal pullback, including the orientation of the segment. -/
theorem segment_linear_term (x : PositiveInput) (u v : RationalUnit) :
    (mul (segmentInverse x u).val
      (sub (realAxis (positiveSegment x v)).val (realAxis (positiveSegment x u)).val)).realPart.Equiv
      (RealRaw.scaleRat (v.val-u.val) (segmentIntegrandValue x u).val) := by
  let I := segmentInverse x u
  let D := realAxis (segmentDisplacement x)
  have hd := mul_equiv I.property I.property
    (sub_valid (realAxis (positiveSegment x v)).property (realAxis (positiveSegment x u)).property)
    (scaleRat_valid D.property) (equiv_refl _ I.property) (positiveSegment_difference x u v)
  have hc : (mul I.val (scaleRat (v.val-u.val) D.val)).Equiv
      (scaleRat (v.val-u.val) (mul D.val I.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid I.property (scaleRat_valid D.property))
      (hright := scaleRat_valid (mul_valid D.property I.property))
    rw [ComplexRawQuotient.ofRaw_mul _ _ I.property (scaleRat_valid D.property),
      ComplexRawQuotient.ofRaw_scaleRat _ _ D.property,
      ComplexRawQuotient.ofRaw_scaleRat _ _ (mul_valid D.property I.property),
      ComplexRawQuotient.ofRaw_mul _ _ D.property I.property,
      ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.mul_comm]
  have hnames := ComplexRaw.scaleRat_equiv (r := v.val-u.val) (segmentIntegrand_embedding x u)
  have hreal := real_embedding_scale (v.val-u.val) (segmentIntegrandValue x u)
  exact realPart_equiv (equiv_trans
    (mul_valid I.property (sub_valid (realAxis (positiveSegment x v)).property (realAxis (positiveSegment x u)).property))
    (mul_valid I.property (scaleRat_valid D.property))
    (ofRealRaw_valid _ (RealRaw.scaleRat_valid (segmentIntegrandValue x u).property)) hd
    (equiv_trans (mul_valid I.property (scaleRat_valid D.property))
      (scaleRat_valid (mul_valid D.property I.property))
      (ofRealRaw_valid _ (RealRaw.scaleRat_valid (segmentIntegrandValue x u).property)) hc
      (equiv_trans (scaleRat_valid (mul_valid D.property I.property))
        (scaleRat_valid (realAxis (segmentIntegrandValue x u)).property)
        (ofRealRaw_valid _ (RealRaw.scaleRat_valid (segmentIntegrandValue x u).property)) hnames hreal)))

/-- Uniform quadratic remainder for the whole positive real segment. -/
theorem segment_log_remainder (x : PositiveInput) (u v : RationalUnit)
    (huv : u.val≤v.val) (hmesh : v.val-u.val≤(segmentMesh x).val) :
    Small (ofRealRaw (RealRaw.sub (RealRaw.sub (log (positivePoint x v)).val (log (positivePoint x u)).val)
      (RealRaw.scaleRat (v.val-u.val) (segmentIntegrandValue x u).val)))
      (segmentRemainderConstant x*(v.val-u.val)^2) := by
  let B := 1/(segmentLower x).val
  let H := segmentBound x*(v.val-u.val)
  have hB : 0≤B := by dsimp [B]; rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr (segmentLower x).property)
  have hstep := segment_difference_small x u v
  rw [qabs_eq_self_of_nonneg (show 0≤v.val-u.val by grind only)] at hstep
  have hs : 2*B*H≤(1:Rat)/128 := by
    have hi1 := Rat.mul_inv_cancel (segmentLower x).val (Rat.ne_of_gt (segmentLower x).property)
    have hi2 := Rat.mul_inv_cancel (segmentBound x) (Rat.ne_of_gt (segmentBound_pos x))
    have hfactor : 0≤2*B*segmentBound x :=
      Rat.mul_nonneg (Rat.mul_nonneg (show (0:Rat)≤2 by decide +kernel) hB) (Rat.le_of_lt (segmentBound_pos x))
    have hm := Rat.mul_le_mul_of_nonneg_left hmesh hfactor
    have heq : 2*B*segmentBound x*(segmentMesh x).val=(1:Rat)/128 := by
      dsimp [B,segmentMesh]
      simp only [Rat.div_def,Rat.inv_mul_rev,Rat.one_mul]
      have he : (256:Rat)⁻¹=1/256 := by decide +kernel
      rw [he]
      grind only
    rw [heq] at hm
    dsimp [H]
    simpa only [Rat.mul_assoc] using hm

  have h := log_increment_error (positivePoint x u) (positivePoint x v) B H hB
    (Rat.mul_nonneg (Rat.le_of_lt (segmentBound_pos x)) (show 0≤v.val-u.val by grind only))
    (segmentInverse_bound x u) hstep hs
  have hc := segment_linear_term x u v
  have hdiff := RealRaw.sub_equiv
    (RealRaw.sub_valid (log (positivePoint x v)).property (log (positivePoint x u)).property)
    (RealRaw.sub_valid (log (positivePoint x v)).property (log (positivePoint x u)).property)
    (realPart_valid (mul_valid (segmentInverse x u).property
      (sub_valid (realAxis (positiveSegment x v)).property (realAxis (positiveSegment x u)).property)))
    (RealRaw.scaleRat_valid (segmentIntegrandValue x u).property)
    (RealRaw.equiv_refl _ (RealRaw.sub_valid (log (positivePoint x v)).property (log (positivePoint x u)).property)) hc
  have he := ofRealRaw_equiv_of_equiv
    (RealRaw.sub_valid (RealRaw.sub_valid (log (positivePoint x v)).property (log (positivePoint x u)).property)
      (realPart_valid (mul_valid (segmentInverse x u).property
        (sub_valid (realAxis (positiveSegment x v)).property (realAxis (positiveSegment x u)).property))))
    (RealRaw.sub_valid (RealRaw.sub_valid (log (positivePoint x v)).property (log (positivePoint x u)).property)
      (RealRaw.scaleRat_valid (segmentIntegrandValue x u).property)) hdiff
  have hh := Small.congr
    (ofRealRaw_valid _ (RealRaw.sub_valid (RealRaw.sub_valid (log (positivePoint x v)).property (log (positivePoint x u)).property)
      (realPart_valid (mul_valid (segmentInverse x u).property
        (sub_valid (realAxis (positiveSegment x v)).property (realAxis (positiveSegment x u)).property)))))
    (ofRealRaw_valid _ (RealRaw.sub_valid (RealRaw.sub_valid (log (positivePoint x v)).property (log (positivePoint x u)).property)
      (RealRaw.scaleRat_valid (segmentIntegrandValue x u).property))) he h
  have heC : 16*(2*B*H)^2=segmentRemainderConstant x*(v.val-u.val)^2 := by
    dsimp [B,H,segmentRemainderConstant]; simp only [Rat.pow_succ,Rat.pow_zero]; grind only
  rw [heC] at hh
  exact hh
end ComputableAnalysis.ExponentialComputations
