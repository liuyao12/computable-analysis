import ComputableAnalysis.SineSquareData
import ComputableAnalysis.CartwrightTrigCalculus
import ComputableAnalysis.ImaginaryExponentialIntegral

/-! Euler's imaginary-exponential construction, with a checked differential
characterization and uniqueness. The integral proof uses exponential integration;
it does not import either squared-trigonometric FTC value proof. -/
namespace ComputableAnalysis.TrigSquareEuler
open ClosedArctanInverse ClockTrigonometry CartwrightMoments FiniteSampleCalculus
open RationalSampleLimits MonotoneAverage IntervalSelections ImaginaryExponentialIntegral

/-- Coordinates of the square of the geometric unit exponential. -/
def re (t : Rat) (q : Nat) : Rat := c t q*c t q-s t q*s t q
def im (t : Rat) (q : Nat) : Rat := 2*s t q*c t q
def frequency (q : Nat) : Rat := 2*frequencySample q

def realModel : Model re (fun t q=> -frequency q*im t q) := by
  apply ((cosineModel.mul cosineModel).add ((Model.const (-1)).mul (sineModel.mul sineModel))).congr
  · intros;unfold re;grind only
  · intros;unfold frequency im;grind only

def imaginaryModel : Model im (fun t q=>frequency q*re t q) := by
  apply ((Model.const 2).mul (sineModel.mul cosineModel)).congr
  · intros;unfold im;grind only
  · intros;unfold frequency re;grind only

/-- Euler's construction solves E'=i*frequency*E; any solution with the same
initial value agrees with it. The conclusion does not assume Euler's identity. -/
theorem euler_unique {R I : SampleFunction}
    (r : Model R (fun t q=> -frequency q*I t q))
    (i : Model I (fun t q=>frequency q*R t q))
    (hr : Close (R 0) (re 0)) (hi : Close (I 0) (im 0))
    {t : Rat} (ht : Unit t) : Close (R t) (re t) ∧ Close (I t) (im t) :=
  solution_unique frequency r i realModel imaginaryModel hr hi ht

theorem euler_cosine_square (t : Rat) (q : Nat) :
    CosineSquare.sample t q=(1+re t q)/2 := by
  have h:=ClockTrigonometry.sample_unit t q
  unfold CosineSquare.sample re;simp only [Rat.div_def];grind only

theorem euler_sine_square (t : Rat) (q : Nat) :
    SineSquare.sample t q=(1-re t q)/2 := by
  have h:=ClockTrigonometry.sample_unit t q
  unfold SineSquare.sample re;simp only [Rat.div_def];grind only

def reciprocal (q : Nat) : Rat := 1/frequency q

theorem reciprocal_bound : Bounded reciprocal 1 := by
  intro q
  have hp:=frequencySample_bounds q
  have hd : 0<frequency q := by unfold frequency;grind only
  have hi : 0<(frequency q)⁻¹ := (Rat.inv_pos).2 hd
  have he:=Rat.mul_inv_cancel (frequency q) (Rat.ne_of_gt hd)
  have hm:=Rat.mul_le_mul_of_nonneg_right (show 1≤frequency q by unfold frequency;grind only) (Rat.le_of_lt hi)
  unfold reciprocal
  rw [Rat.div_def,Rat.one_mul,qabs_eq_self_of_nonneg (Rat.le_of_lt hi)]
  grind only

theorem reciprocal_cancel (q : Nat) : reciprocal q*frequency q=1 := by
  have h:=frequencySample_bounds q
  have hn : frequency q≠0 := by unfold frequency;grind only
  unfold reciprocal;rw [Rat.div_def,Rat.one_mul,Rat.inv_mul_cancel _ hn]

private theorem left_constant (v a b : Rat) (n : Nat) : left (fun _=>v) a b n=v := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [left,ih,Rat.div_def];grind

theorem real_sum (a b : Rat) (d q : Nat) :
    left (fun t=>re t q) a b d=2*left (fun t=>CosineSquare.sample t q) a b d-1 := by
  have he : (fun t=>re t q)=(fun t=>2*CosineSquare.sample t q-1) := by
    funext t;have h:=euler_cosine_square t q;simp only [Rat.div_def] at h;grind only
  rw [he,left_sub,left_mul,left_constant]

def sumSample (q : Nat) : Rat := 2*CosineSquare.sumSample q-1

theorem mesh_comparison (d q : Nat) (hdq : d≤q) :
    qabs (sumSample q-left (fun t=>re t q) 0 1 d)≤2*meshRadius d := by
  rw [real_sum]
  have he : sumSample q-(2*left (fun t=>CosineSquare.sample t q) 0 1 d-1)=
      2*(CosineSquare.sumSample q-left (fun t=>CosineSquare.sample t q) 0 1 d) := by unfold sumSample;grind only
  rw [he,qabs_mul,show qabs (2:Rat)=2 by decide +kernel]
  exact Rat.mul_le_mul_of_nonneg_left (CosineSquare.mesh_comparison d q hdq) (by decide +kernel)

theorem integral_exponential : Close sumSample
    (fun q=>reciprocal q*im 1 q-reciprocal q*im 0 q) :=
  integrate_real imaginaryModel 1 (by decide +kernel) reciprocal_bound reciprocal_cancel
    sumSample 2 (by decide +kernel) mesh_comparison

theorem imaginary_endpoint_zero {t : Rat} (ht : t=0 ∨ t=1) : Small (im t) := by
  apply small_of_geometric_bound 112 (by decide +kernel)
  intro q
  have h:=ClockTrigonometry.sample_endpoint ht q
  have hb:=ClockTrigonometry.sample_bounds t q
  rcases ht with rfl | rfl
  · have hs : qabs (s 0 q)≤28*meshRadius q := by simpa only [show ∀ a:Rat,a-0=a by intros;grind] using h.2
    have hc : qabs (c 0 q)≤1 := by rw [qabs_eq_self_of_nonneg hb.1];exact hb.2.1
    have he:=mul_abs_bound (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤28) (Rat.le_of_lt (meshRadius_pos q))) hs hc
    unfold im;rw [Rat.mul_assoc,qabs_mul,show qabs (2:Rat)=2 by decide +kernel]
    have h2:=Rat.mul_le_mul_of_nonneg_left he (by decide +kernel : (0:Rat)≤2)
    have hp:=meshRadius_pos q
    grind only
  · have hc : qabs (c 1 q)≤56*meshRadius q := by simpa only [show (1:Rat)-1=0 by decide +kernel,show ∀ a:Rat,a-0=a by intros;grind] using h.1
    have hs : qabs (s 1 q)≤1 := by rw [qabs_eq_self_of_nonneg hb.2.2.1];exact hb.2.2.2
    have he:=mul_abs_bound (by decide +kernel : (0:Rat)≤1) hs hc
    unfold im;rw [Rat.mul_assoc,qabs_mul,show qabs (2:Rat)=2 by decide +kernel]
    have h2:=Rat.mul_le_mul_of_nonneg_left he (by decide +kernel : (0:Rat)≤2)
    grind only

theorem real_initial_one : Close (re 0) (fun _=>1) := by
  have hs : Small (s 0) := by
    apply small_of_geometric_bound 28 (by decide +kernel)
    intro q
    simpa only [show ∀ a:Rat,a-0=a by intros;grind] using
      (ClockTrigonometry.sample_endpoint (Or.inl rfl) q).2
  have hb : Bounded (s 0) 1 := by
    intro q
    have h:=ClockTrigonometry.sample_bounds 0 q
    rw [qabs_eq_self_of_nonneg h.2.2.1];exact h.2.2.2
  have h:=small_bounded_mul (by decide +kernel : (0:Rat)≤2)
    (show Bounded (fun _=>(-2:Rat)) 2 from fun _=>by exact (by decide +kernel : qabs (-2:Rat)≤2))
    (small_bounded_mul (by decide +kernel) hb hs)
  have he : (fun q=>(-2:Rat)*(s 0 q*s 0 q))=(fun q=>re 0 q-1) := by
    funext q;have h:=ClockTrigonometry.sample_unit 0 q;unfold re;grind only
  rw [he] at h;exact h

/-- The normalized imaginary exponential is uniquely characterized by E(0)=1
and its differential equation. This is a differential, not a power-series,
construction of the exponential on the chart. -/
theorem euler_characterization {R I : SampleFunction}
    (r : Model R (fun t q=> -frequency q*I t q))
    (i : Model I (fun t q=>frequency q*R t q))
    (hr : Close (R 0) (fun _=>1)) (hi : Close (I 0) (fun _=>0))
    {t : Rat} (ht : Unit t) : Close (R t) (re t) ∧ Close (I t) (im t) :=
  euler_unique r i (close_trans hr (close_symm real_initial_one))
    (close_trans hi (close_symm (close_zero_of_small (imaginary_endpoint_zero (Or.inl rfl))))) ht

theorem endpoint_zero : Small (fun q=>reciprocal q*im 1 q-reciprocal q*im 0 q) :=
  small_sub (small_bounded_mul (by decide +kernel) reciprocal_bound (imaginary_endpoint_zero (Or.inr rfl)))
    (small_bounded_mul (by decide +kernel) reciprocal_bound (imaginary_endpoint_zero (Or.inl rfl)))

theorem cosine_sum : Close CosineSquare.sumSample (fun _=>1/2) := by
  have h:=close_scale (1/2) (close_trans integral_exponential (close_zero_of_small endpoint_zero))
  have he : ∀ q, (1/2:Rat)*sumSample q-(1/2)*0=CosineSquare.sumSample q-1/2 := by
    intro q;unfold sumSample;simp only [Rat.div_def];grind only
  change Small _ at h ⊢
  simpa only [he] using h

theorem cosine_integral_via_Euler : CosineSquare.integral.Equiv (RealRaw.ofRat (1/4)) :=
  CosineSquare.normalize_value (equiv_of_close CosineSquare.quarterIntegral_valid (RealRaw.ofRat_valid _)
    CosineSquare.sumSample (fun _=>1/2) CosineSquare.sumSample_mem (rat_mem _) cosine_sum)

theorem sine_integral_via_Euler : SineSquare.integral.Equiv (RealRaw.ofRat (1/4)) := by
  have h:=close_sub (close_refl (fun _=>(1:Rat))) cosine_sum
  have hs : Close SineSquare.sumSample (fun _=>1/2) := by
    simpa only [←SineSquare.sumSample_complement,show (1:Rat)-1/2=1/2 by decide +kernel] using h
  exact SineSquare.normalize_value (equiv_of_close SineSquare.quarterIntegral_valid (RealRaw.ofRat_valid _)
    SineSquare.sumSample (fun _=>1/2) SineSquare.sumSample_mem (rat_mem _) hs)

end ComputableAnalysis.TrigSquareEuler
