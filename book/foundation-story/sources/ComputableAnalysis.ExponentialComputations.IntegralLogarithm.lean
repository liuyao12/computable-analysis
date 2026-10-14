import ComputableAnalysis.ExponentialComputations.SegmentFTC

/-! The reciprocal integral on the whole positive real axis. Arbitrary
represented endpoints are pulled back to [0,1], retaining orientation. The
runtime uses finite rectangle sums; both inverse laws are proved. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions ModularForms
set_option maxHeartbeats 1000000

def segmentLogValue (x : PositiveInput) (t : Rat) : RealRaw :=
  if ht : 0≤t ∧ t≤1 then (log (positivePoint x ⟨t,ht⟩)).val else RealRaw.ofRat 0

def reciprocalBounds (x : PositiveInput) (eps : QPos) : Integral.Bounds (segmentIntegrand x) :=
  lipschitzBounds (segmentIntegrand x) rfl rfl (segmentVariation x) (segmentVariation_nonnegative x)
    (segmentIntegrand_lipschitz x) eps

theorem reciprocalBounds_gap (x : PositiveInput) (eps : QPos) :
    (reciprocalBounds x eps).upperSum-(reciprocalBounds x eps).lowerSum≤eps.val :=
  lipschitzBounds_gap (segmentIntegrand x) rfl rfl _ _ _ eps

theorem segmentIntegrand_bound (x : PositiveInput) (t : RationalUnit) :
    Small (realAxis (segmentIntegrandValue x t)).val (2*segmentBound x*(1/(segmentLower x).val)) := by
  have hR : 0≤1/(segmentLower x).val := by
    rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr (segmentLower x).property)
  exact Small.congr
    (mul_valid (realAxis (segmentDisplacement x)).property (segmentInverse x t).property)
    (realAxis (segmentIntegrandValue x t)).property (segmentIntegrand_embedding x t)
    (Small.mul (realAxis (segmentDisplacement x)).property (segmentInverse x t).property
      (Rat.le_of_lt (segmentBound_pos x)) hR (scalar_small _) (segmentInverse_bound x t))

theorem segmentLog_cellBounds (x : PositiveInput) :
    Integral.CellDerivativeBounds (segmentIntegrand x) (segmentLogValue x) := by
  apply cellBounds_of_quadratic (segmentIntegrand x) (segmentLogValue x) rfl rfl
    (fun t ht0 ht1 => by simp only [segmentLogValue,dif_pos (And.intro ht0 ht1)]; exact (log _).property)
    (segmentRemainderConstant x) (by
      dsimp [segmentRemainderConstant]
      exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (Rat.le_of_lt (segmentBound_pos x))))
        (Rat.pow_nonneg (by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr (segmentLower x).property))))
    (segmentMesh x) (2*segmentBound x*(1/(segmentLower x).val))
  · intro t ht n
    have h := segmentIntegrand_bound x ⟨t,ht⟩
    rw [segmentIntegrand_compute x ⟨t,ht⟩ n]
    exact ⟨h.1 0 n,h.2.1 n 0⟩
  · intro u v hu hu0 huv hv1 hmesh
    have hum : 0≤u ∧ u≤1 := ⟨hu0,by grind only⟩
    have hvm : 0≤v ∧ v≤1 := ⟨by grind only,hv1⟩
    have h := segment_log_remainder x ⟨u,hum⟩ ⟨v,hvm⟩ huv hmesh
    have hcompute : (segmentIntegrand x).compute u hu = (segmentIntegrandValue x ⟨u,hum⟩).val.compute := by
      funext n
      exact segmentIntegrand_compute x ⟨u,hum⟩ n
    simpa only [Small,RealRaw.Le,ofRealRaw,realPart,imagPart,RealRaw.sub,RealRaw.subCompute,
      RealRaw.scaleRat,RealRaw.scaleRatCompute,segmentLogValue,dif_pos hum,dif_pos hvm,hcompute] using h

/-- A concrete existence proof for the integral; the endpoint law follows
from finite subdivision and tight reciprocal bounds. -/
theorem segmentLog_hasIntegral (x : PositiveInput) : Integral.HasIntegral (segmentIntegrand x)
    (RealRaw.sub (segmentLogValue x 1) (segmentLogValue x 0)) :=
  (segmentLog_cellBounds x).hasIntegral (by change (0:Rat)≤1; decide +kernel)
    (fun eps => ⟨reciprocalBounds x eps,reciprocalBounds_gap x eps⟩)

def oneInput : PositiveInput := ⟨⟨RealRaw.ofRat 1,RealRaw.ofRat_valid _⟩,⟨0,by decide +kernel⟩⟩
def zeroInput : RealInput := ⟨RealRaw.ofRat 0,RealRaw.ofRat_valid _⟩

theorem exp_zero : (exp zeroInput).val.Equiv oneInput.val.val := realPart_equiv entireExponential_zero

theorem log_one : (log oneInput).val.Equiv zeroInput.val :=
  RealRaw.equiv_symm (log_unique oneInput zeroInput exp_zero)

theorem positiveSegment_zero (x : PositiveInput) :
    (positiveSegment x ⟨0,by decide +kernel⟩).val.Equiv oneInput.val.val := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  simp only [positiveSegment,RealRaw.add,RealRaw.addCompute,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    RealRaw.ofRat,if_pos (show (0:Rat)≤0 by decide +kernel),Rat.zero_mul,Rat.add_zero,oneInput,show (1:Rat)-0=1 by decide +kernel]
  exact ⟨Rat.le_refl,Rat.le_refl⟩

theorem positiveSegment_one (x : PositiveInput) :
    (positiveSegment x ⟨1,by decide +kernel⟩).val.Equiv x.val.val := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid _ x.val.property n
  simp only [positiveSegment,RealRaw.add,RealRaw.addCompute,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    RealRaw.ofRat,if_pos (show (0:Rat)≤1 by decide +kernel),Rat.one_mul,Rat.sub_self,Rat.zero_add]
  exact ⟨ho,ho⟩

theorem segmentLog_endpoint (x : PositiveInput) :
    (RealRaw.sub (segmentLogValue x 1) (segmentLogValue x 0)).Equiv (log x).val := by
  have h0 := RealRaw.equiv_trans (log (positivePoint x ⟨0,by decide +kernel⟩)).property
    (log oneInput).property zeroInput.property
    (log_congr _ _ (positiveSegment_zero x)) log_one
  have h1 := log_congr (positivePoint x ⟨1,by decide +kernel⟩) x (positiveSegment_one x)
  have h0' : (segmentLogValue x 0).Equiv zeroInput.val := by
    change (log (positivePoint x ⟨0,by decide +kernel⟩)).val.Equiv zeroInput.val
    exact h0
  have h1' : (segmentLogValue x 1).Equiv (log x).val := by
    change (log (positivePoint x ⟨1,by decide +kernel⟩)).val.Equiv (log x).val
    exact h1
  have hv0 : (segmentLogValue x 0).Valid := (log (positivePoint x ⟨0,by decide +kernel⟩)).property
  have hv1 : (segmentLogValue x 1).Valid := (log (positivePoint x ⟨1,by decide +kernel⟩)).property
  have hh := RealRaw.sub_equiv (x := segmentLogValue x 1) (x' := (log x).val)
    (y := segmentLogValue x 0) (y' := zeroInput.val) hv1 (log x).property hv0 zeroInput.property h1' h0'
  have hz : (RealRaw.sub (log x).val zeroInput.val).Equiv (log x).val := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
    have ho := RealRaw.interval_order_of_valid _ (log x).property n
    change ((log x).val.compute n).lo-(0:Rat)≤((log x).val.compute n).hi ∧
      ((log x).val.compute n).lo≤((log x).val.compute n).hi-(0:Rat)
    constructor <;> grind only
  exact RealRaw.equiv_trans (RealRaw.sub_valid hv1 hv0)
    (RealRaw.sub_valid (log x).property zeroInput.property) (log x).property hh hz

/-- Independent rectangle-sum computation of the normalized reciprocal
integral. The pullback is (x-1)/(1+t(x-1)), so x<1 is oriented correctly. -/
def integralLog (x : PositiveInput) : RealInput :=
  ⟨rectangleValue (segmentIntegrand x) (reciprocalBounds x),
    rectangleValue_valid _ _ (reciprocalBounds_gap x) _ (segmentLog_hasIntegral x)⟩

theorem integralLog_hasIntegral (x : PositiveInput) :
    Integral.HasIntegral (segmentIntegrand x) (integralLog x).val :=
  rectangleValue_hasIntegral _ _ (reciprocalBounds_gap x) _ (segmentLog_hasIntegral x)

/-- Exact global identification of the reciprocal integral with logarithm. -/
theorem integralLog_equiv_log (x : PositiveInput) : (integralLog x).val.Equiv (log x).val :=
  RealRaw.equiv_trans (integralLog x).property (segmentLog_hasIntegral x).valid (log x).property
    (rectangleValue_agrees _ _ _ (segmentLog_hasIntegral x)) (segmentLog_endpoint x)

theorem integralLog_congr (x y : PositiveInput) (h : x.val.val.Equiv y.val.val) :
    (integralLog x).val.Equiv (integralLog y).val :=
  RealRaw.equiv_trans (integralLog x).property (log x).property (integralLog y).property
    (integralLog_equiv_log x) (RealRaw.equiv_trans (log x).property (log y).property
      (integralLog y).property (log_congr x y h) (RealRaw.equiv_symm (integralLog_equiv_log y)))

/-- Exponential is an actual two-sided inverse of the constructed integral. -/
theorem integralLog_exp (x : RealInput) :
    (integralLog ⟨exp x,exp_positive x⟩).val.Equiv x.val :=
  RealRaw.equiv_trans (integralLog _).property (log _).property x.property (integralLog_equiv_log _) (log_exp x)

theorem exp_integralLog (x : PositiveInput) : (exp (integralLog x)).val.Equiv x.val.val :=
  RealRaw.equiv_trans (exp (integralLog x)).property (exp (log x)).property x.val.property
    (exp_congr _ _ (integralLog_equiv_log x)) (exp_log x)

/-- Any real computation inverted by the reciprocal integral agrees with
exponential; this law supports independently justified inversion methods. -/
theorem exp_unique_of_integralLog (x : RealInput) (y : PositiveInput)
    (h : (integralLog y).val.Equiv x.val) : y.val.val.Equiv (exp x).val :=
  exp_unique_of_log x y (RealRaw.equiv_trans (log y).property (integralLog y).property x.property
    (RealRaw.equiv_symm (integralLog_equiv_log y)) h)
end ComputableAnalysis.ExponentialComputations
