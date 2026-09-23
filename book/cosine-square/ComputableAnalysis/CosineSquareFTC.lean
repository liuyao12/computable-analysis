import ComputableAnalysis.CosineSquareData
import ComputableAnalysis.CartwrightTrigCalculus

/-! A second proof of the same numerical program, by product differentiation
and the finite-sample FTC. The symmetry integral proof is not imported. -/
namespace ComputableAnalysis.CosineSquare
open ClosedArctanInverse ClockTrigonometry MonotoneAverage IntervalSelections
open CartwrightMoments FiniteSampleCalculus RationalSampleLimits

/-- Reciprocal pi sample: frequencySample is pi/2 in quarter-turn coordinates. -/
def reciprocalSample (q : Nat) : Rat := 1/(2*frequencySample q)

theorem reciprocalSample_unit (q : Nat) : Unit (reciprocalSample q) := by
  have hp:=frequencySample_bounds q
  have hd : 0<2*frequencySample q := by grind only
  have hi : 0<(2*frequencySample q)⁻¹ := (Rat.inv_pos).2 hd
  have he:=Rat.mul_inv_cancel (2*frequencySample q) (Rat.ne_of_gt hd)
  have hm:=Rat.mul_le_mul_of_nonneg_right
    (show 1≤2*frequencySample q by grind only) (Rat.le_of_lt hi)
  simp only [reciprocalSample,Rat.div_def,Rat.one_mul]
  exact ⟨Rat.le_of_lt hi,by grind only⟩

def primitiveSample (t : Rat) (q : Nat) : Rat :=
  t/2+reciprocalSample q*s t q*c t q

/-- Product-rule construction of the primitive derivative; it contains no
integral-value hypothesis. -/
def primitiveModel : Model primitiveSample sample := by
  let coefficient := Model.constant reciprocalSample 1 (by decide +kernel) (fun q=>by
    rw [qabs_eq_self_of_nonneg (reciprocalSample_unit q).1]
    exact (reciprocalSample_unit q).2)
  apply (((Model.const (1/2)).mul Model.identity).add
    (coefficient.mul (sineModel.mul cosineModel))).congr
  · intro t q
    change (1/2:Rat)*t+reciprocalSample q*(s t q*c t q)=primitiveSample t q
    unfold primitiveSample
    simp only [Rat.div_def]
    grind only
  · intro t q
    change (0*t+(1/2:Rat)*1)+(0*(s t q*c t q)+
      reciprocalSample q*((frequencySample q*c t q)*c t q+s t q*(-frequencySample q*s t q)))=sample t q
    have hp:=frequencySample_bounds q
    have hd : 0<2*frequencySample q := by grind only
    have he:=Rat.inv_mul_cancel (2*frequencySample q) (Rat.ne_of_gt hd)
    have hc:=ClockTrigonometry.sample_unit t q
    unfold reciprocalSample sample
    simp only [Rat.div_def,Rat.one_mul] at *
    grind only

/-- The displayed primitive in the public x coordinate. -/
def normalizedPrimitiveSample (x : Rat) (q : Nat) : Rat := primitiveSample (2*x) q/2

theorem normalizedPrimitive_formula (x : Rat) (q : Nat) :
    normalizedPrimitiveSample x q=x/2+reciprocalSample q*s (2*x) q*c (2*x) q/2 := by
  unfold normalizedPrimitiveSample primitiveSample
  simp only [Rat.div_def]
  grind only

/-- A finite derivative certificate for every rational cell of the public
half interval, not merely an identity at the two final endpoints. -/
theorem normalizedPrimitive_local_error {a b : Rat}
    (ha : GeometricSineDerivative.OnHalf a)
    (hb : GeometricSineDerivative.OnHalf b) (hab : a<b) :
    ∃ N, ∀ q, N≤q →
      qabs (normalizedPrimitiveSample b q-normalizedPrimitiveSample a q-
        (b-a)*sample (2*a) q) ≤ 2*primitiveModel.errorBound*(b-a)*(b-a) := by
  have ha' : Unit (2*a) := by have a0:=ha.1;have a1:=ha.2;simp only [Rat.div_def] at a1;constructor <;> grind only
  have hb' : Unit (2*b) := by have b0:=hb.1;have b1:=hb.2;simp only [Rat.div_def] at b1;constructor <;> grind only
  obtain ⟨N,hN⟩:=primitiveModel.local_error (2*a) (2*b) ha' hb' (by grind only)
  refine ⟨N,fun q hq=>?_⟩
  have h:=hN q hq
  have e : normalizedPrimitiveSample b q-normalizedPrimitiveSample a q-(b-a)*sample (2*a) q=
    (1/2:Rat)*(primitiveSample (2*b) q-primitiveSample (2*a) q-(2*b-2*a)*sample (2*a) q) := by
      unfold normalizedPrimitiveSample;simp only [Rat.div_def];grind only
  rw [e,qabs_mul,show qabs (1/2:Rat)=1/2 by decide +kernel]
  have hm:=Rat.mul_le_mul_of_nonneg_left h (by decide +kernel : (0:Rat)≤1/2)
  simp only [Rat.div_def] at hm ⊢
  grind only

theorem primitive_endpoints_close :
    Close (fun q=>primitiveSample 1 q-primitiveSample 0 q) (fun _=>1/2) := by
  apply small_of_geometric_bound 84 (by decide +kernel)
  intro q
  have h0:=(ClockTrigonometry.sample_endpoint (t:=0) (Or.inl rfl) q).2
  have h1:=(ClockTrigonometry.sample_endpoint (t:=1) (Or.inr rfl) q).1
  simp only [show (1:Rat)-1=0 by decide +kernel, show ∀ x:Rat, x-0=x by intro x;grind] at h0 h1
  have b0:=ClockTrigonometry.sample_bounds 0 q
  have b1:=ClockTrigonometry.sample_bounds 1 q
  have hr:=reciprocalSample_unit q
  have rabs : qabs (reciprocalSample q)≤1 := by rw [qabs_eq_self_of_nonneg hr.1];exact hr.2
  have sabs : qabs (s 1 q)≤1 := by rw [qabs_eq_self_of_nonneg b1.2.2.1];exact b1.2.2.2
  have cabs : qabs (c 0 q)≤1 := by rw [qabs_eq_self_of_nonneg b0.1];exact b0.2.1
  have p1:=mul_abs_bound (by decide +kernel : (0:Rat)≤1)
    (by simpa only [Rat.one_mul] using mul_abs_bound (by decide +kernel : (0:Rat)≤1) rabs sabs) h1
  have p0:=mul_abs_bound (by decide +kernel : (0:Rat)≤1) rabs
    (mul_abs_bound (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤28)
      (Rat.le_of_lt (meshRadius_pos q))) h0 cabs)
  have ht:=qabs_sub_le (reciprocalSample q*s 1 q*c 1 q)
    (reciprocalSample q*(s 0 q*c 0 q))
  change qabs ((primitiveSample 1 q-primitiveSample 0 q)-1/2)≤84*meshRadius q
  have he : (primitiveSample 1 q-primitiveSample 0 q)-1/2=
    reciprocalSample q*s 1 q*c 1 q-reciprocalSample q*(s 0 q*c 0 q) := by
    unfold primitiveSample;simp only [Rat.div_def];grind only
  rw [he]
  grind only

theorem sumSample_via_FTC : Close sumSample (fun _=>1/2) := by
  have h:=chosen_samples_FTC primitiveModel sumSample 1 (by decide +kernel) (by
    intro d q hdq
    simpa only [Rat.one_mul] using mesh_comparison d q hdq)
  exact close_trans h primitive_endpoints_close

theorem quarterIntegral_via_FTC : quarterIntegral.Equiv (RealRaw.ofRat (1/2)) :=
  equiv_of_close quarterIntegral_valid (RealRaw.ofRat_valid _)
    sumSample (fun _=>1/2) sumSample_mem (rat_mem _) sumSample_via_FTC

/-- The normalized squared-cosine integral, by the native finite FTC. -/
theorem integral_via_FTC : integral.Equiv (RealRaw.ofRat (1/4)) := by
  exact normalize_value quarterIntegral_via_FTC

end ComputableAnalysis.CosineSquare
