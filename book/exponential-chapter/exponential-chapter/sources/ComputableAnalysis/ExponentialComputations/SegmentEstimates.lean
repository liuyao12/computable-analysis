import ComputableAnalysis.ExponentialComputations.PositiveSegment

/-! Uniform finite error bounds on the positive reciprocal pullback. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions ModularForms
set_option maxHeartbeats 1000000

private def valueClass (z : Scalar) := ComplexRawQuotient.ofRaw z.val z.property

theorem real_embedding_scale (r : Rat) (x : RealInput) :
    (scaleRat r (realAxis x).val).Equiv (realAxis ⟨RealRaw.scaleRat r x.val,RealRaw.scaleRat_valid x.property⟩).val := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid (RealRaw.scaleRat r x.val) (RealRaw.scaleRat_valid x.property) n
  simp only [realAxis,ofRealRaw,scaleRat,QBox.scaleRat,RealRaw.scaleRat,RealRaw.scaleRatCompute,Rat.mul_zero]
  simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute] at ho
  by_cases hr : 0≤r
  all_goals
    simp only [hr,if_true,if_false] at ho ⊢
    constructor <;> constructor <;> first | exact ho | exact Rat.le_refl

theorem small_signed_scale (z : Scalar) (r B : Rat) (h : Small z.val B) :
    Small (scaleRat r z.val) (qabs r*B) := by
  by_cases hr : 0≤r
  · rw [qabs_eq_self_of_nonneg hr]; exact small_scale hr h
  · have hnr : 0≤ -r := by grind only
    have hs := SeriesLimitLaws.small_neg (small_scale hnr h)
    have he : (neg (scaleRat (-r) z.val)).Equiv (scaleRat r z.val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := neg_valid (scaleRat_valid z.property)) (hright := scaleRat_valid z.property)
      rw [ComplexRawQuotient.ofRaw_neg _ (scaleRat_valid z.property),
        ComplexRawQuotient.ofRaw_scaleRat _ _ z.property,
        ComplexRawQuotient.ofRaw_scaleRat _ _ z.property,ComplexRawQuotient.neg_scaleRat]
      rw [Rat.neg_neg]
    have hq : qabs r= -r := by unfold qabs; rw [if_pos (show r<0 by grind only)]
    rw [hq]
    exact Small.congr (neg_valid (scaleRat_valid z.property)) (scaleRat_valid z.property) he hs

theorem segment_difference_small (x : PositiveInput) (u v : RationalUnit) :
    Small (sub (realAxis (positiveSegment x v)).val (realAxis (positiveSegment x u)).val)
      (segmentBound x*qabs (v.val-u.val)) := by
  have h := small_signed_scale (realAxis (segmentDisplacement x)) (v.val-u.val)
    (segmentBound x) (scalar_small _)
  have hs := Small.congr (scaleRat_valid (realAxis (segmentDisplacement x)).property)
    (sub_valid (realAxis (positiveSegment x v)).property (realAxis (positiveSegment x u)).property)
    (equiv_symm (positiveSegment_difference x u v)) h
  simpa only [Rat.mul_comm] using hs

def segmentInverse (x : PositiveInput) (t : RationalUnit) : Scalar :=
  RepresentedReciprocal.inverse (realAxis (positiveSegment x t))
    (positive_real_nonzero (positiveSegment x t) (positivePoint x t).property)

theorem segmentInverse_real (x : PositiveInput) (t : RationalUnit) :
    (segmentInverse x t).val.Equiv (realAxis (segmentReciprocal x t)).val :=
  positive_inverse_agreement (positivePoint x t) (segmentLower x) (positiveSegment_lower x t)

theorem segmentInverse_bound (x : PositiveInput) (t : RationalUnit) :
    Small (segmentInverse x t).val (1/(segmentLower x).val) :=
  Small.congr (realAxis (segmentReciprocal x t)).property (segmentInverse x t).property
    (equiv_symm (segmentInverse_real x t))
    (positiveReciprocal_embedding_small _ (positiveSegment x t).property (segmentLower x).val
      (segmentLower x).property (positiveSegment_lower x t))

theorem segmentIntegrand_embedding (x : PositiveInput) (t : RationalUnit) :
    (mul (realAxis (segmentDisplacement x)).val (segmentInverse x t).val).Equiv
      (realAxis (segmentIntegrandValue x t)).val :=
  equiv_trans (mul_valid (realAxis (segmentDisplacement x)).property (segmentInverse x t).property)
    (mul_valid (realAxis (segmentDisplacement x)).property (realAxis (segmentReciprocal x t)).property)
    (realAxis (segmentIntegrandValue x t)).property
    (mul_equiv (realAxis (segmentDisplacement x)).property (realAxis (segmentDisplacement x)).property
      (segmentInverse x t).property (realAxis (segmentReciprocal x t)).property
      (equiv_refl _ (realAxis (segmentDisplacement x)).property) (segmentInverse_real x t))
    (real_embedding_mul _ _ (segmentDisplacement x).property (segmentReciprocal x t).property)

def segmentVariation (x : PositiveInput) : Rat :=
  8*(segmentBound x)^2*(1/(segmentLower x).val)^2

theorem segmentIntegrand_variation (x : PositiveInput) (u v : RationalUnit) :
    Small (sub (realAxis (segmentIntegrandValue x v)).val (realAxis (segmentIntegrandValue x u)).val)
      (segmentVariation x*qabs (v.val-u.val)) := by
  let U := realAxis (positiveSegment x u)
  let V := realAxis (positiveSegment x v)
  let A := segmentInverse x u
  let B := segmentInverse x v
  let D := realAxis (segmentDisplacement x)
  let R := 1/(segmentLower x).val
  let H := qabs (v.val-u.val)
  have hR : 0≤R := by dsimp [R]; rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr (segmentLower x).property)
  have hD := Rat.le_of_lt (segmentBound_pos x)
  have hH := qabs_nonneg (v.val-u.val)
  have hdiff := segment_difference_small x v u
  rw [show qabs (u.val-v.val)=qabs (v.val-u.val) by rw [show u.val-v.val= -(v.val-u.val) by grind only,qabs_neg]] at hdiff
  have hprod := Small.mul B.property (sub_valid U.property V.property) hR (Rat.mul_nonneg hD hH)
    (segmentInverse_bound x v) hdiff
  have hprod2 := Small.mul (mul_valid B.property (sub_valid U.property V.property)) A.property
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) (Rat.mul_nonneg hD hH)) hR
    hprod (segmentInverse_bound x u)
  have hall := Small.mul D.property (mul_valid (mul_valid B.property (sub_valid U.property V.property)) A.property)
    hD (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) (Rat.mul_nonneg hD hH))) hR)
    (scalar_small D) hprod2
  have ha := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid U.property A.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse U (positive_real_nonzero (positiveSegment x u) (positivePoint x u).property))
  have hb := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid V.property B.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse V (positive_real_nonzero (positiveSegment x v) (positivePoint x v).property))
  have hprodEq : (mul D.val (mul (mul B.val (sub U.val V.val)) A.val)).Equiv
      (sub (mul D.val B.val) (mul D.val A.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid D.property (mul_valid (mul_valid B.property (sub_valid U.property V.property)) A.property))
      (hright := sub_valid (mul_valid D.property B.property) (mul_valid D.property A.property))
    change valueClass U*valueClass A=1 at ha
    change valueClass V*valueClass B=1 at hb
    change valueClass D*((valueClass B*(valueClass U-valueClass V))*valueClass A)=
      valueClass D*valueClass B-valueClass D*valueClass A
    grind only
  have hnames := FunctionTheory.sub_congr (segmentIntegrand_embedding x v) (segmentIntegrand_embedding x u)
  have he := equiv_trans
    (mul_valid D.property (mul_valid (mul_valid B.property (sub_valid U.property V.property)) A.property))
    (sub_valid (mul_valid D.property B.property) (mul_valid D.property A.property))
    (sub_valid (realAxis (segmentIntegrandValue x v)).property (realAxis (segmentIntegrandValue x u)).property)
    hprodEq hnames
  have hh := Small.congr
    (mul_valid D.property (mul_valid (mul_valid B.property (sub_valid U.property V.property)) A.property))
    (sub_valid (realAxis (segmentIntegrandValue x v)).property (realAxis (segmentIntegrandValue x u)).property) he hall
  have hc : 2*segmentBound x*(2*(2*R*(segmentBound x*H))*R)=segmentVariation x*H := by
    dsimp [segmentVariation]; simp only [Rat.pow_succ,Rat.pow_zero]; grind only
  change Small _ (2*segmentBound x*(2*(2*R*(segmentBound x*H))*R)) at hh
  rw [hc] at hh
  exact hh
end ComputableAnalysis.ExponentialComputations
