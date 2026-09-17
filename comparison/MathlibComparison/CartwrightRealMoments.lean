import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import ComputableAnalysis.CartwrightArithmetic

/-! The analytic middle of the Cartwright argument on [0,1].
No existing irrationality theorem is imported or used. -/
namespace MathlibComparison.Cartwright
open Real intervalIntegral
open ComputableAnalysis.CartwrightArithmetic
noncomputable section

def lambda : ℝ := Real.pi / 2

def moment (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, (1-x^2)^n * Real.cos (lambda*x)

lemma lambda_pos : 0 < lambda := by unfold lambda; positivity
lemma lambda_le_two : lambda ≤ 2 := by unfold lambda; linarith [Real.pi_le_four]
lemma sin_lambda : Real.sin lambda = 1 := Real.sin_pi_div_two
lemma cos_lambda : Real.cos lambda = 0 := Real.cos_pi_div_two
lemma moment_continuous (n : ℕ) : Continuous (fun x:ℝ => (1-x^2)^n * Real.cos (lambda*x)) := by fun_prop

lemma moment_zero : lambda * moment 0 = 1 := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f:=Real.cos) (a:=(0:ℝ)) (b:=1) lambda
  simpa [moment, sin_lambda] using h

/-- This is a single FTC application to the first polynomial-trigonometric primitive. -/
lemma moment_one : lambda^2 * moment 1 = 2 * moment 0 := by
  let F : ℝ → ℝ := fun x => lambda*(1-x^2)*Real.sin (lambda*x) - 2*x*Real.cos (lambda*x)
  let D : ℝ → ℝ := fun x => (lambda^2*(1-x^2)-2)*Real.cos (lambda*x)
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hd (x : ℝ) : HasDerivAt F (D x) x := by
    dsimp [F,D]
    convert! (((((hasDerivAt_id x).pow 2).const_sub 1).const_mul lambda).mul
      ((hasDerivAt_id x).const_mul lambda).sin).sub
      (((hasDerivAt_id x).const_mul 2).mul (((hasDerivAt_id x).const_mul lambda).cos)) using 1 <;> (try funext y) <;> (try simp only [Pi.pow_apply, Pi.mul_apply, id_eq]) <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hD.intervalIntegrable 0 1)
  have he : (∫ x in (0:ℝ)..1, D x) = lambda^2 * moment 1 - 2*moment 0 := by
    have hfun : D = fun x => lambda^2*((1-x^2)*Real.cos (lambda*x))-2*Real.cos (lambda*x) := by
      funext x; dsimp [D]; ring
    rw [hfun,intervalIntegral.integral_sub]
    · simp only [intervalIntegral.integral_const_mul,moment,pow_one,pow_zero,one_mul]
    · exact (by fun_prop : Continuous (fun x:ℝ => lambda^2*((1-x^2)*Real.cos (lambda*x)))).intervalIntegrable 0 1
    · exact (by fun_prop : Continuous (fun x:ℝ => 2*Real.cos (lambda*x))).intervalIntegrable 0 1
  rw [he] at h
  simp [F,cos_lambda] at h
  linarith

/-- Two integrations by parts, retaining explicit endpoint terms until simplification. -/
lemma moment_recurrence (n : ℕ) :
    lambda^2 * moment (n+2) =
      2*(n+2:ℝ)*(2*n+3)*moment (n+1) - 4*(n+2:ℝ)*(n+1)*moment n := by
  let f (x : ℝ) := 1-x^2
  let u₁ (x : ℝ) := f x^(n+2)
  let u₁' (x : ℝ) := -(2*(n+2:ℝ)*x*f x^(n+1))
  let v₁ (x : ℝ) := Real.sin (lambda*x)
  let v₁' (x : ℝ) := Real.cos (lambda*x)*lambda
  let u₂ (x : ℝ) := x*f x^(n+1)
  let u₂' (x : ℝ) := f x^(n+1)-2*(n+1:ℝ)*x^2*f x^n
  let v₂ (x : ℝ) := Real.cos (lambda*x)
  let v₂' (x : ℝ) := -Real.sin (lambda*x)*lambda
  have hf (x : ℝ) : HasDerivAt f (-2*x) x := by
    convert! ((hasDerivAt_id x).pow 2).const_sub 1 using 1 <;> (try funext y) <;> (try simp [f, id_eq, Pi.pow_apply, Pi.mul_apply]) <;> (try ring)
  have hu₁ (x : ℝ) : HasDerivAt u₁ (u₁' x) x := by
    convert! (hf x).pow (n+2) using 1 <;> (try funext y) <;> (try simp [u₁,u₁',id_eq, Pi.pow_apply, Pi.mul_apply]) <;> (try ring)
  have hv₁ (x : ℝ) : HasDerivAt v₁ (v₁' x) x := by
    convert! ((hasDerivAt_id x).const_mul lambda).sin using 1 <;> (try funext y) <;> (try simp [v₁,v₁',id_eq, Pi.pow_apply, Pi.mul_apply]) <;> (try ring)
  have hu₂ (x : ℝ) : HasDerivAt u₂ (u₂' x) x := by
    convert! (hasDerivAt_id x).mul ((hf x).pow (n+1)) using 1 <;> (try funext y) <;> (try simp [u₂,u₂',id_eq, Pi.pow_apply, Pi.mul_apply]) <;> (try ring)
  have hv₂ (x : ℝ) : HasDerivAt v₂ (v₂' x) x := by
    convert! ((hasDerivAt_id x).const_mul lambda).cos using 1 <;> (try funext y) <;> (try simp [v₂,v₂',id_eq, Pi.pow_apply, Pi.mul_apply]) <;> (try ring)
  have h₁ := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a:=(0:ℝ)) (b:=1)
    (fun x _ => hu₁ x) (fun x _ => hv₁ x)
    ((by dsimp [u₁',f]; fun_prop : Continuous u₁').intervalIntegrable 0 1)
    ((by dsimp [v₁']; fun_prop : Continuous v₁').intervalIntegrable 0 1)
  have h₂ := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a:=(0:ℝ)) (b:=1)
    (fun x _ => hu₂ x) (fun x _ => hv₂ x)
    ((by dsimp [u₂',f]; fun_prop : Continuous u₂').intervalIntegrable 0 1)
    ((by dsimp [v₂']; fun_prop : Continuous v₂').intervalIntegrable 0 1)
  have e₁ : (∫ x in (0:ℝ)..1, u₁ x*v₁' x) = lambda*moment (n+2) := by
    unfold moment; rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; dsimp [u₁,v₁',f]; ring
  have e₂ : (∫ x in (0:ℝ)..1, u₁' x*v₁ x) = -2*(n+2:ℝ)*(∫ x in (0:ℝ)..1, u₂ x*v₁ x) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; dsimp [u₁',u₂]; ring
  have e₃ : (∫ x in (0:ℝ)..1, u₂ x*v₂' x) = -lambda*(∫ x in (0:ℝ)..1, u₂ x*v₁ x) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; dsimp [v₂',v₁]; ring
  have e₄ : (∫ x in (0:ℝ)..1, u₂' x*v₂ x) =
      (2*n+3:ℝ)*moment (n+1)-2*(n+1:ℝ)*moment n := by
    have he (x : ℝ) : u₂' x*v₂ x = (2*n+3:ℝ)*((1-x^2)^(n+1)*Real.cos (lambda*x)) -
        2*(n+1:ℝ)*((1-x^2)^n*Real.cos (lambda*x)) := by
      dsimp [u₂',v₂,f]; rw [pow_succ]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_sub]
    · simp only [intervalIntegral.integral_const_mul,moment]
    · exact ((moment_continuous (n+1)).const_mul _).intervalIntegrable 0 1
    · exact ((moment_continuous n).const_mul _).intervalIntegrable 0 1
  rw [e₁,e₂] at h₁
  rw [e₃,e₄] at h₂
  simp [u₁,u₂,v₁,v₂,f,cos_lambda] at h₁ h₂
  have h₃ := congrArg (fun z : ℝ => lambda*z) h₁
  have h₄ := congrArg (fun z : ℝ => (-2*(n+2:ℝ))*z) h₂
  nlinarith only [h₃,h₄]

lemma weight_bounds (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ (1-x^2)^n ∧ (1-x^2)^n ≤ 1 := by
  have ha : 0 ≤ 1-x^2 := by nlinarith [hx.1,hx.2]
  exact ⟨pow_nonneg ha n, pow_le_one₀ ha (by nlinarith [sq_nonneg x])⟩

lemma moment_upper (n : ℕ) : moment n ≤ 1 := by
  have hm := intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) (a:=(0:ℝ)) (b:=1) (by norm_num)
    ((moment_continuous n).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1)
    (g:=fun _ : ℝ => 1) (fun x hx => ?_)
  · simpa [moment] using hm
  · have hw := weight_bounds n hx
    exact le_trans (mul_le_mul_of_nonneg_left (Real.cos_le_one _) hw.1) (by simpa using hw.2)

lemma moment_positive (n : ℕ) : 0 < moment n := by
  apply intervalIntegral.integral_pos (by norm_num : (0:ℝ)<1) (moment_continuous n).continuousOn
  · intro x hx
    have hw := (weight_bounds n ⟨le_of_lt hx.1,hx.2⟩).1
    have hc : 0 ≤ Real.cos (lambda*x) := Real.cos_nonneg_of_mem_Icc ⟨by
      have hp := mul_nonneg (le_of_lt lambda_pos) (le_of_lt hx.1)
      linarith [Real.pi_pos], by
      dsimp [lambda]
      nlinarith [Real.pi_pos, hx.2]⟩
    exact mul_nonneg hw hc
  · exact ⟨0,by norm_num,by simp⟩

end
end MathlibComparison.Cartwright
