import ComputableAnalysis.SineSquareFTC
import ComputableAnalysis.TrigSquareEuler
import ComputableAnalysis.CosinePrimitiveEndpoints

/-! Variable rational endpoints in a quarter-turn chart. These computations
are the local pieces of the represented-endpoint construction. -/
namespace ComputableAnalysis.TrigSquareVariable
open ClosedArctanInverse ClockTrigonometry CartwrightMoments FiniteSampleCalculus
open RationalSampleLimits MonotoneAverage IntervalSelections

private theorem mul_unit {a b : Rat} (ha : Unit a) (hb : Unit b) : Unit (a*b) := by
  have h:=Rat.mul_le_mul_of_nonneg_left hb.2 ha.1
  exact ⟨Rat.mul_nonneg ha.1 hb.1,by grind only⟩

def data (t : Rat) (ht : Unit t) : MonotoneSampleIntegral.Data where
  sample := fun u q=>CosineSquare.sample (t*u) q
  bound := fun u q hu=>CosineSquare.sample_bounds (t*u) q
  decreasing := by
    intro q a b ha hb hab
    exact CosineSquare.sample_decreases q (t*a) (t*b) (mul_unit ht ha) (mul_unit ht hb)
      (Rat.mul_le_mul_of_nonneg_left hab ht.1)
  errorConstant := 112
  evaluation_error := fun u hu q r=>CosineSquare.evaluation_error (t*u) (mul_unit ht hu) q r

/-- The signed length factor belongs to the computation, not to an assumed answer. -/
def integral (t : Rat) (ht : Unit t) : RealRaw := RealRaw.scaleRat t (MonotoneSampleIntegral.raw (data t ht))
def sumSample (t : Rat) (q : Nat) : Rat := t*left (fun u=>CosineSquare.sample (t*u) q) 0 1 q

theorem integral_valid (t : Rat) (ht : Unit t) : (integral t ht).Valid :=
  RealRaw.scaleRat_valid (MonotoneSampleIntegral.valid (data t ht))

theorem sumSample_mem (t : Rat) (ht : Unit t) (q : Nat) :
    InBox (sumSample t q) ((integral t ht).compute q) :=
  scale_mem (MonotoneSampleIntegral.contains_future (data t ht) q q (Nat.le_refl q)) ht.1

/-- Sine-square quadrature obtained by complementing each rectangle. -/
def sineIntegral (t : Rat) (ht : Unit t) : RealRaw := RealRaw.ofRat t-integral t ht

def sineSumSample (t : Rat) (q : Nat) : Rat :=
  t*left (fun u=>SineSquare.sample (t*u) q) 0 1 q

private theorem left_constant (v a b : Rat) (n : Nat) : left (fun _=>v) a b n=v := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [left,ih,Rat.div_def];grind

theorem sine_sum_complement (t : Rat) (q : Nat) : sineSumSample t q=t-sumSample t q := by
  have he : (fun u=>SineSquare.sample (t*u) q)=(fun u=>1-CosineSquare.sample (t*u) q) := by
    funext u;exact SineSquare.sample_complement _ _
  unfold sineSumSample sumSample
  rw [he,left_sub,left_constant];grind only

theorem sineIntegral_valid (t : Rat) (ht : Unit t) : (sineIntegral t ht).Valid :=
  RealRaw.sub_valid (RealRaw.ofRat_valid _) (integral_valid t ht)

theorem sineSumSample_mem (t : Rat) (ht : Unit t) (q : Nat) :
    InBox (sineSumSample t q) ((sineIntegral t ht).compute q) := by
  rw [sine_sum_complement]
  exact sub_mem (rat_mem t q) (sumSample_mem t ht q)

/-- Affine restriction of a finite derivative model, including the zero endpoint. -/
def rescale {F D : SampleFunction} (M : Model F D) (t : Rat) (ht : Unit t) :
    Model (fun u q=>F (t*u) q) (fun u q=>t*D (t*u) q) where
  valueBound := M.valueBound
  slopeBound := M.slopeBound
  errorBound := M.errorBound
  valueBound_nonneg := M.valueBound_nonneg
  slopeBound_nonneg := M.slopeBound_nonneg
  errorBound_nonneg := M.errorBound_nonneg
  value := fun u q hu=>M.value (t*u) q (mul_unit ht hu)
  slope := by
    intro u q hu
    rw [qabs_mul,qabs_eq_self_of_nonneg ht.1]
    have h:=Rat.mul_le_mul_of_nonneg_left (M.slope (t*u) q (mul_unit ht hu)) ht.1
    have h1:=Rat.mul_le_mul_of_nonneg_right ht.2 M.slopeBound_nonneg
    grind only
  local_error := by
    intro a b ha hb hab
    by_cases hzero : t=0
    · subst t
      refine ⟨0,fun q hq=>?_⟩
      simp only [Rat.zero_mul,Rat.mul_zero,show ∀ a:Rat,a-a-0=0 by intros;grind,show qabs (0:Rat)=0 by decide +kernel]
      exact Rat.mul_nonneg (Rat.mul_nonneg M.errorBound_nonneg (by grind)) (by grind)
    · have htpos : 0<t := by have h:=ht.1;grind only
      obtain ⟨N,hN⟩:=M.local_error (t*a) (t*b) (mul_unit ht ha) (mul_unit ht hb)
        (Rat.mul_lt_mul_of_pos_left hab htpos)
      refine ⟨N,fun q hq=>?_⟩
      have h:=hN q hq
      have he : t*b-t*a=t*(b-a) := by grind only
      rw [he] at h
      have hsq:=Rat.mul_le_mul_of_nonneg_left ht.2 ht.1
      have hcoef : 0≤M.errorBound*(b-a)*(b-a) :=
        Rat.mul_nonneg (Rat.mul_nonneg M.errorBound_nonneg (by grind)) (by grind)
      have hm:=Rat.mul_le_mul_of_nonneg_left (show t*t≤1 by grind only) hcoef
      have hh : (b-a)*(t*D (t*a) q)=t*(b-a)*D (t*a) q := by grind only
      rw [hh]
      grind only

theorem mesh_comparison (t : Rat) (ht : Unit t) (d q : Nat) (hdq : d≤q) :
    qabs (sumSample t q-left (fun u=>t*CosineSquare.sample (t*u) q) 0 1 d)≤meshRadius d := by
  rw [left_mul]
  have he : sumSample t q-t*left (fun u=>CosineSquare.sample (t*u) q) 0 1 d=
      -t*(left (fun u=>CosineSquare.sample (t*u) q) 0 1 d-left (fun u=>CosineSquare.sample (t*u) q) 0 1 q) := by
    unfold sumSample;grind only
  rw [he,qabs_mul,qabs_neg,qabs_eq_self_of_nonneg ht.1]
  have hm:=mesh_error (fun u=>CosineSquare.sample (t*u) q) ((data t ht).decreasing q)
    (CosineSquare.sample_bounds (t*1) q).1 (CosineSquare.sample_bounds (t*0) q).2 hdq
  have h1:=Rat.mul_le_mul_of_nonneg_left hm ht.1
  have h2:=Rat.mul_le_mul_of_nonneg_right ht.2 (Rat.le_of_lt (meshRadius_pos d))
  grind only

theorem sum_FTC (t : Rat) (ht : Unit t) : Close (sumSample t)
    (fun q=>CosineSquare.primitiveSample t q-CosineSquare.primitiveSample 0 q) := by
  have h:=chosen_samples_FTC (rescale CosineSquare.primitiveModel t ht) (sumSample t) 1
    (by decide +kernel) (by intro d q hdq;simpa only [Rat.one_mul] using mesh_comparison t ht d q hdq)
  simpa only [Rat.mul_one,Rat.mul_zero] using h

/-- A separately evaluated endpoint formula in quarter-turn coordinates. -/
def endpoint (t : Rat) : RealRaw := (RealRaw.ofRat (t/2)) +
  (RealRaw.mul CosinePrimitive.inversePi (RealRaw.mul (sine t) (cosine t)))

theorem endpoint_valid (t : Rat) (ht : Unit t) : (endpoint t).Valid :=
  RealRaw.add_valid (RealRaw.ofRat_valid _) (RealRaw.mul_valid CosinePrimitive.inversePi_valid
    (RealRaw.mul_valid (sine_valid ht) (cosine_valid ht)))

theorem reciprocal_mem (q : Nat) : InBox (CosineSquare.reciprocalSample q) (CosinePrimitive.inversePi.compute q) := by
  have hp:=pi_stage_bounds q
  have he : CosineSquare.reciprocalSample q=1/(piCircleArea.compute q).lo := by
    unfold CosineSquare.reciprocalSample frequencySample
    congr 1;simp only [Rat.div_def];grind only
  rw [he,CosinePrimitive.inversePi_compute]
  change InBox (1/(piCircleArea.compute q).lo) (QInterval.inv (piCircleArea.compute q))
  have ho:=RealRaw.interval_order_of_valid CosinePrimitive.inversePi CosinePrimitive.inversePi_valid q
  rw [CosinePrimitive.inversePi_compute] at ho
  change (QInterval.inv (piCircleArea.compute q)).lo≤(QInterval.inv (piCircleArea.compute q)).hi at ho
  unfold QInterval.inv at ho
  rw [if_pos (show 0<(piCircleArea.compute q).lo by grind only)] at ho
  unfold QInterval.inv
  rw [if_pos (show 0<(piCircleArea.compute q).lo by grind only)]
  exact ⟨ho,Rat.le_refl⟩

theorem endpoint_mem (t : Rat) (ht : Unit t) (q : Nat) :
    InBox (CosineSquare.primitiveSample t q) ((endpoint t).compute q) := by
  have h:=ClockTrigonometry.add_mem (rat_mem (t/2) q)
    (mul_mem (reciprocal_mem q) (mul_mem (s_mem ht q) (c_mem ht q)))
  simpa only [endpoint,CosineSquare.primitiveSample,Rat.mul_assoc] using h

theorem initial_zero : Small (CosineSquare.primitiveSample 0) := by
  have h:=small_bounded_mul (by decide +kernel : (0:Rat)≤1) TrigSquareEuler.reciprocal_bound
    (TrigSquareEuler.imaginary_endpoint_zero (Or.inl rfl))
  have hh:=small_bounded_mul (by decide +kernel : (0:Rat)≤1)
    (show Bounded (fun _=>(1/2:Rat)) 1 from fun q=>by exact (by decide +kernel : qabs (1/2:Rat)≤1)) h
  have he : (fun q=>(1/2:Rat)*(TrigSquareEuler.reciprocal q*TrigSquareEuler.im 0 q))=
      CosineSquare.primitiveSample 0 := by
    funext q;unfold CosineSquare.primitiveSample CosineSquare.reciprocalSample
      TrigSquareEuler.reciprocal TrigSquareEuler.frequency TrigSquareEuler.im
    simp only [Rat.div_def];grind only
  rw [he] at hh;exact hh

/-- Euler's exponential integration law yields the same endpoint model via
power reduction. The product-rule square model is not used here. -/
def eulerEndpointModel : Model CosineSquare.primitiveSample CosineSquare.sample := by
  let E := ImaginaryExponentialIntegral.realEndpointModel TrigSquareEuler.imaginaryModel
    1 (by decide +kernel) TrigSquareEuler.reciprocal_bound TrigSquareEuler.reciprocal_cancel
  apply (((Model.const (1/2)).mul Model.identity).add ((Model.const (1/2)).mul E)).congr
  · intro t q
    change (1/2:Rat)*t+(1/2)*(TrigSquareEuler.reciprocal q*TrigSquareEuler.im t q)=_
    unfold CosineSquare.primitiveSample CosineSquare.reciprocalSample
      TrigSquareEuler.reciprocal TrigSquareEuler.frequency TrigSquareEuler.im
    simp only [Rat.div_def];grind only
  · intro t q
    change (0*t+(1/2:Rat)*1)+(0*(TrigSquareEuler.reciprocal q*TrigSquareEuler.im t q)+
      (1/2)*TrigSquareEuler.re t q)=_
    rw [TrigSquareEuler.euler_cosine_square]
    simp only [Rat.div_def];grind only

theorem sum_Euler (t : Rat) (ht : Unit t) : Close (sumSample t)
    (fun q=>CosineSquare.primitiveSample t q-CosineSquare.primitiveSample 0 q) := by
  have h:=chosen_samples_FTC (rescale eulerEndpointModel t ht) (sumSample t) 1
    (by decide +kernel) (by intro d q hdq;simpa only [Rat.one_mul] using mesh_comparison t ht d q hdq)
  simpa only [Rat.mul_one,Rat.mul_zero] using h

theorem definite_integral_of_sums (t : Rat) (ht : Unit t)
    (h : Close (sumSample t) (fun q=>CosineSquare.primitiveSample t q-CosineSquare.primitiveSample 0 q)) :
    (integral t ht).Equiv (endpoint t) := by
  have he : Close (fun q=>CosineSquare.primitiveSample t q-CosineSquare.primitiveSample 0 q)
      (CosineSquare.primitiveSample t) := by
    have h:=small_neg initial_zero
    have hi : (fun q=>(CosineSquare.primitiveSample t q-CosineSquare.primitiveSample 0 q)-CosineSquare.primitiveSample t q)=
        (fun q=> -CosineSquare.primitiveSample 0 q) := by funext q;grind only
    unfold Close;rw [hi];exact h
  exact equiv_of_close (integral_valid t ht) (endpoint_valid t ht)
    (sumSample t) (CosineSquare.primitiveSample t) (sumSample_mem t ht) (endpoint_mem t ht)
    (close_trans h he)

theorem definite_integral (t : Rat) (ht : Unit t) : (integral t ht).Equiv (endpoint t) :=
  definite_integral_of_sums t ht (sum_FTC t ht)

theorem definite_integral_via_Euler (t : Rat) (ht : Unit t) : (integral t ht).Equiv (endpoint t) :=
  definite_integral_of_sums t ht (sum_Euler t ht)

end ComputableAnalysis.TrigSquareVariable
