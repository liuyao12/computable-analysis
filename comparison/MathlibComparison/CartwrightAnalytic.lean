import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! The Mathlib analytic route. The moment recurrence is derived by integration
by parts, without using Mathlib's irrational-pi theorem or private moment lemmas. -/
namespace MathlibComparison.CartwrightAnalytic
open Real intervalIntegral

noncomputable def frequency : ℝ := Real.pi/2
noncomputable def c (t : ℝ) : ℝ := Real.cos (frequency*t)
noncomputable def s (t : ℝ) : ℝ := Real.sin (frequency*t)
def weight (n : Nat) (t : ℝ) : ℝ := (1-t*t)^n
noncomputable def moment (n : Nat) : ℝ := ∫ t in (0:ℝ)..1, weight n t*c t
noncomputable def auxSine (n : Nat) : ℝ := ∫ t in (0:ℝ)..1, (t*weight n t)*s t

lemma continuous_c : Continuous c := by unfold c;fun_prop
lemma continuous_s : Continuous s := by unfold s;fun_prop
lemma continuous_weight (n : Nat) : Continuous (weight n) := by unfold weight;fun_prop
lemma c_derivative (x : ℝ) : HasDerivAt c (-frequency*s x) x := by
  unfold c s
  convert! ((hasDerivAt_id x).const_mul frequency).cos using 1 <;> simp only [id_eq] <;> ring
lemma s_derivative (x : ℝ) : HasDerivAt s (frequency*c x) x := by
  unfold c s
  convert! ((hasDerivAt_id x).const_mul frequency).sin using 1 <;> simp only [id_eq] <;> ring
lemma s_one : s 1=1 := by simp [s,frequency]
lemma s_zero : s 0=0 := by simp [s]
lemma c_one : c 1=0 := by simp [c,frequency]
lemma c_zero : c 0=1 := by simp [c]

lemma sine_parts {f df : ℝ→ℝ} (hf : ∀x,HasDerivAt f (df x) x) (hd : Continuous df) :
    frequency*(∫x in (0:ℝ)..1,f x*c x)+(∫x in (0:ℝ)..1,df x*s x)=f 1 := by
  have hc : Continuous (fun x=>frequency*c x) := continuous_const.mul continuous_c
  have h:=intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a:=(0:ℝ)) (b:=1) (fun x _=>hf x) (fun x _=>s_derivative x)
    (hd.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  rw [s_one,s_zero,mul_one,mul_zero,sub_zero] at h
  have he : (∫x in (0:ℝ)..1,f x*(frequency*c x))=frequency*(∫x in (0:ℝ)..1,f x*c x) := by
    rw [←intervalIntegral.integral_const_mul]
    congr 1;funext x;ring
  rw [he] at h
  linarith

lemma cosine_parts {f df : ℝ→ℝ} (hf : ∀x,HasDerivAt f (df x) x) (hd : Continuous df) :
    (∫x in (0:ℝ)..1,df x*c x)-frequency*(∫x in (0:ℝ)..1,f x*s x)= -f 0 := by
  have hc : Continuous (fun x=> -frequency*s x) := continuous_const.mul continuous_s
  have h:=intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a:=(0:ℝ)) (b:=1) (fun x _=>hf x) (fun x _=>c_derivative x)
    (hd.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  rw [c_one,c_zero,mul_one,mul_zero,zero_sub] at h
  have he : (∫x in (0:ℝ)..1,f x*(-frequency*s x))= -frequency*(∫x in (0:ℝ)..1,f x*s x) := by
    rw [←intervalIntegral.integral_const_mul]
    congr 1;funext x;ring
  rw [he] at h
  linarith

lemma weight_derivative (n : Nat) (x : ℝ) :
    HasDerivAt (weight (n+1)) (-2*(n+1)*x*weight n x) x := by
  have h : HasDerivAt (fun t:ℝ=>1-t*t) (-2*x) x := by
    convert! ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_sub 1 using 1 <;> simp only [id_eq] <;> ring
  unfold weight
  convert! h.pow (n+1) using 1 <;> simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] <;> ring

lemma first_parts (n : Nat) :
    frequency*moment (n+1)-2*(n+1)*auxSine n=0 := by
  have hd : Continuous (fun x:ℝ=> -2*(n+1)*x*weight n x) := by unfold weight;fun_prop
  have h:=sine_parts (weight_derivative n) hd
  have hw : weight (n+1) 1=0 := by simp [weight]
  rw [hw] at h
  have he : (∫x in (0:ℝ)..1,(-2*(n+1)*x*weight n x)*s x)= -2*(n+1)*auxSine n := by
    unfold auxSine
    rw [←intervalIntegral.integral_const_mul]
    congr 1;funext x;ring
  rw [he] at h
  change frequency*moment (n+1)+_ =0 at h
  linarith

lemma second_parts_zero : moment 0-frequency*auxSine 0=0 := by
  have h:=cosine_parts (fun x=>hasDerivAt_id x) continuous_const
  simpa [moment,auxSine,weight] using h

lemma aux_derivative (n : Nat) (x : ℝ) :
    HasDerivAt (fun t=>t*weight (n+1) t)
      ((2*(n+1)+1)*weight (n+1) x-2*(n+1)*weight n x) x := by
  convert! (hasDerivAt_id x).mul (weight_derivative n x) using 1
  simp only [id_eq]
  unfold weight
  rw [pow_succ]
  ring

lemma second_parts (n : Nat) :
    (2*(n+1)+1)*moment (n+1)-2*(n+1)*moment n-frequency*auxSine (n+1)=0 := by
  have hd : Continuous (fun x:ℝ=>(2*(n+1)+1)*weight (n+1) x-2*(n+1)*weight n x) := by unfold weight;fun_prop
  have h:=cosine_parts (aux_derivative n) hd
  simp only [zero_mul,neg_zero] at h
  have he : (∫x in (0:ℝ)..1,((2*(n+1)+1)*weight (n+1) x-2*(n+1)*weight n x)*c x)=
      (2*(n+1)+1)*moment (n+1)-2*(n+1)*moment n := by
    have hA : IntervalIntegrable (fun x:ℝ=>(2*(n+1)+1)*(weight (n+1) x*c x)) MeasureTheory.volume 0 1 :=
      (continuous_const.mul ((continuous_weight (n+1)).mul continuous_c)).intervalIntegrable _ _
    have hB : IntervalIntegrable (fun x:ℝ=>2*(n+1)*(weight n x*c x)) MeasureTheory.volume 0 1 :=
      (continuous_const.mul ((continuous_weight n).mul continuous_c)).intervalIntegrable _ _
    calc
      _ = ∫x in (0:ℝ)..1, (2*(n+1)+1)*(weight (n+1) x*c x)-2*(n+1)*(weight n x*c x) := by
        congr 1;funext x;ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hA hB,
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
        rfl
  rw [he] at h
  exact h

lemma base_zero : frequency*moment 0=1 := by
  have h:=sine_parts (fun x=>hasDerivAt_const x (1:ℝ)) continuous_const
  simpa [moment,weight] using h

lemma base_one : frequency^3*moment 1=2 := by
  have h0:=base_zero
  have h1:=first_parts 0
  have h2:=second_parts_zero
  norm_num at h1
  linear_combination frequency^2*h1-2*frequency*h2+2*h0

lemma recurrence (n : Nat) :
    frequency^2*moment (n+2)=2*(n+2)*(2*n+3)*moment (n+1)-4*(n+1)*(n+2)*moment n := by
  have h1:=first_parts (n+1)
  have h2:=second_parts n
  push_cast at h1 h2 ⊢
  linear_combination frequency*h1-2*(n+2)*h2

end MathlibComparison.CartwrightAnalytic
