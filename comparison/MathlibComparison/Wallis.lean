import MathlibComparison.CartwrightMomentBridge
import ComputableAnalysis.WallisLaws

/-! Mathlib proves the SAME native cosine-power evaluation. Quadrature
correspondence uses rectangle bounds, not the Wallis evaluation or recurrence. -/
namespace MathlibComparison.Wallis
open ComputableAnalysis ClosedArctanInverse Filter Topology
open MathlibComparison.Cartwright

noncomputable def moment (n : Nat) : ℝ :=
  ∫ x in (0:ℝ)..1, Real.cos (lambda*x)^n

lemma samples_tendsto (n : Nat) (x : Rat) (hx : Unit x) :
    Tendsto (fun q=>(ComputableAnalysis.Wallis.sample n x q:ℝ)) atTop
      (𝓝 (Real.cos (lambda*(x:ℝ))^n)) := by
  simpa only [ComputableAnalysis.Wallis.sample,Rat.cast_pow] using (cosine_samples_tendsto x hx).pow n

lemma integrand_antitone (n : Nat) :
    AntitoneOn (fun x:ℝ=>Real.cos (lambda*x)^n) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  apply pow_le_pow_left₀ (MathlibComparison.Cartwright.cosine_nonnegative hy)
  exact Real.cos_le_cos_of_nonneg_of_le_pi
    (mul_nonneg (le_of_lt lambda_pos) hx.1)
    (by unfold lambda;nlinarith [hy.2,Real.pi_pos])
    (mul_le_mul_of_nonneg_left hxy (le_of_lt lambda_pos))

lemma integral_samples_tendsto (n : Nat) :
    Tendsto (fun q=>(ComputableAnalysis.Wallis.integralSample n q:ℝ)) atTop (𝓝 (moment n)) := by
  apply RealDyadicAverages.diagonal_tendsto (ComputableAnalysis.Wallis.sample n)
    (fun x:ℝ=>Real.cos (lambda*x)^n) (samples_tendsto n)
    (by fun_prop) (integrand_antitone n) (by simp) (by simp [cos_lambda])
  exact ComputableAnalysis.Wallis.mesh_error n

/-- The bridge identifies the actual supplied numerical program. -/
theorem integral_represents (n : Nat) :
    Represents (ComputableAnalysis.Wallis.integral n) (moment n) :=
  represents_of_tendsto (ComputableAnalysis.Wallis.integral_valid n)
    (ComputableAnalysis.Wallis.integralSample n) (ComputableAnalysis.Wallis.integral_mem n)
    (integral_samples_tendsto n)

lemma change_variable (n : Nat) :
    lambda*moment n=∫ x in (0:ℝ)..lambda, Real.cos x^n := by
  have h:=intervalIntegral.mul_integral_comp_mul_left (f:=fun x:ℝ=>Real.cos x^n)
    (a:=(0:ℝ)) (b:=1) lambda
  simpa only [moment,mul_zero,mul_one] using h

lemma moment_zero : moment 0=1 := by simp [moment]
lemma moment_one : lambda*moment 1=1 := by
  simp only [change_variable,pow_one]
  rw [integral_cos,sin_lambda,Real.sin_zero,sub_zero]

/-- This dependency is Mathlib's integration-by-parts formula, not a native law. -/
lemma moment_recurrence (n : Nat) :
    ((n+2:Nat):ℝ)*moment (n+2)=((n+1:Nat):ℝ)*moment n := by
  have h:=integral_cos_pow_aux (n:=n) (a:=(0:ℝ)) (b:=lambda)
  rw [cos_lambda,zero_pow (Nat.succ_ne_zero _),Real.sin_zero,zero_mul,mul_zero,sub_zero,zero_add,
    ←change_variable (n+2),←change_variable n] at h
  have hp:=lambda_pos
  push_cast at h ⊢
  nlinarith

theorem lawsViaMathlib : ComputableAnalysis.Wallis.Laws where
  zero := by
    apply small_of_tendsto_zero
    have h:=(integral_samples_tendsto 0).sub (tendsto_const_nhds (x:=(1:ℝ)))
    simpa only [moment_zero,sub_self,Rat.cast_sub,Rat.cast_one] using h
  one := by
    apply small_of_tendsto_zero
    have h:=(frequency_samples_tendsto.mul (integral_samples_tendsto 1)).sub
      (tendsto_const_nhds (x:=(1:ℝ)))
    simpa only [moment_one,sub_self,Rat.cast_sub,Rat.cast_mul,Rat.cast_one] using h
  recurrence := by
    intro n
    apply small_of_tendsto_zero
    have h:=((integral_samples_tendsto (n+2)).const_mul ((n+2:Nat):ℝ)).sub
      ((integral_samples_tendsto n).const_mul ((n+1:Nat):ℝ))
    have he : ((n+2:Nat):ℝ)*moment (n+2)-((n+1:Nat):ℝ)*moment n=0 := by rw [moment_recurrence,sub_self]
    simpa only [ComputableAnalysis.Wallis.recurrenceSample,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,he] using h

end MathlibComparison.Wallis

namespace ComputableAnalysis.Wallis

theorem evaluation_viaMathlib (n : Nat) : Statement n :=
  evaluation_of_laws MathlibComparison.Wallis.lawsViaMathlib n

end ComputableAnalysis.Wallis
