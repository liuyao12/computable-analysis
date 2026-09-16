import MathlibComparison.RealLipschitzAverages
import MathlibComparison.CartwrightMomentBridge
import ComputableAnalysis.BetaLaws

/-! The same beta quadratures, evaluated independently through Mathlib FTC.
The correspondence uses finite-cell bounds, not the proposed beta value. -/
namespace MathlibComparison.BetaIntegral
open ComputableAnalysis ClosedArctanInverse Filter Topology

noncomputable def integrand (m n : Nat) (x : ℝ) : ℝ := x^m*(1-x)^n
noncomputable def moment (m n : Nat) : ℝ := ∫ x in (0:ℝ)..1, integrand m n x

private lemma power_difference (n : Nat) {x y : ℝ}
    (hx : x∈Set.Icc (0:ℝ) 1) (hy : y∈Set.Icc (0:ℝ) 1) :
    |x^n-y^n|≤(n:ℝ)*|x-y| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x^(n+1)-y^(n+1)=x^n*(x-y)+(x^n-y^n)*y := by ring
    rw [he]
    have hp : |x^n|≤1 := by rw [abs_of_nonneg (pow_nonneg hx.1 _)];exact pow_le_one₀ hx.1 hx.2
    have hq : |y|≤1 := by rw [abs_of_nonneg hy.1];exact hy.2
    have h1:=mul_le_mul_of_nonneg_right hp (abs_nonneg (x-y))
    have h2:=mul_le_mul_of_nonneg_left hq (abs_nonneg (x^n-y^n))
    have h:=abs_add_le (x^n*(x-y)) ((x^n-y^n)*y)
    simp only [abs_mul] at h
    push_cast;nlinarith

lemma integrand_continuous (m n : Nat) : Continuous (integrand m n) := by
  unfold integrand;fun_prop

lemma integrand_lipschitz (m n : Nat) (x y : ℝ)
    (hx : x∈Set.Icc (0:ℝ) 1) (hy : y∈Set.Icc (0:ℝ) 1) :
    |integrand m n x-integrand m n y|≤((m+n:Nat):ℝ)*|x-y| := by
  have cx : 1-x∈Set.Icc (0:ℝ) 1 := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have cy : 1-y∈Set.Icc (0:ℝ) 1 := ⟨by linarith [hy.2],by linarith [hy.1]⟩
  have h1:=power_difference m hx hy
  have h2:=power_difference n cx cy
  rw [show 1-x-(1-y)= -(x-y) by ring,abs_neg] at h2
  have p : |(1-x)^n|≤1 := by rw [abs_of_nonneg (pow_nonneg cx.1 _)];exact pow_le_one₀ cx.1 cx.2
  have q : |y^m|≤1 := by rw [abs_of_nonneg (pow_nonneg hy.1 _)];exact pow_le_one₀ hy.1 hy.2
  have he : integrand m n x-integrand m n y=
      (x^m-y^m)*(1-x)^n+y^m*((1-x)^n-(1-y)^n) := by unfold integrand;ring
  rw [he]
  have a:=mul_le_mul_of_nonneg_left p (abs_nonneg (x^m-y^m))
  have b:=mul_le_mul_of_nonneg_right q (abs_nonneg ((1-x)^n-(1-y)^n))
  have h:=abs_add_le ((x^m-y^m)*(1-x)^n) (y^m*((1-x)^n-(1-y)^n))
  simp only [abs_mul] at h
  push_cast;nlinarith

lemma samples_tendsto (m n : Nat) :
    Tendsto (fun q=>(ComputableAnalysis.BetaIntegral.sample m n q:ℝ)) atTop (𝓝 (moment m n)) := by
  apply RealLipschitzAverages.samples_tendsto (ComputableAnalysis.BetaIntegral.data m n) (integrand m n)
  · intro x;simp only [ComputableAnalysis.BetaIntegral.data,ComputableAnalysis.BetaIntegral.integrand,
      integrand,Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_one]
  · exact integrand_continuous m n
  · exact integrand_lipschitz m n

/-- All-stage representation of the actual native beta integral program. -/
theorem integral_represents (m n : Nat) :
    Represents (ComputableAnalysis.BetaIntegral.integral m n) (moment m n) :=
  represents_of_tendsto (ComputableAnalysis.BetaIntegral.integral_valid m n)
    (ComputableAnalysis.BetaIntegral.sample m n) (ComputableAnalysis.BetaIntegral.sample_mem m n)
    (samples_tendsto m n)

lemma moment_base (m : Nat) : ((m+1:Nat):ℝ)*moment m 0=1 := by
  simp only [moment,integrand,pow_zero,mul_one]
  rw [integral_pow]
  simp only [one_pow,zero_pow (Nat.succ_ne_zero _),sub_zero]
  push_cast
  field_simp

lemma derivative (m n : Nat) (x : ℝ) :
    HasDerivAt (integrand (m+1) (n+1))
      (((m+1:Nat):ℝ)*integrand m (n+1) x-((n+1:Nat):ℝ)*integrand (m+1) n x) x := by
  have h:=((hasDerivAt_id x).pow (m+1)).mul (((hasDerivAt_id x).const_sub 1).pow (n+1))
  convert! h using 1 <;> simp [integrand] <;> ring

lemma moment_parts (m n : Nat) :
    ((m+1:Nat):ℝ)*moment m (n+1)-((n+1:Nat):ℝ)*moment (m+1) n=0 := by
  have h:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=(0:ℝ)) (b:=1) (fun x _=>derivative m n x)
    ((show Continuous (fun x:ℝ=>((m+1:Nat):ℝ)*integrand m (n+1) x-
      ((n+1:Nat):ℝ)*integrand (m+1) n x) by unfold integrand;fun_prop).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub
      ((integrand_continuous m (n+1)).const_mul _ |>.intervalIntegrable _ _)
      ((integrand_continuous (m+1) n).const_mul _ |>.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  simpa only [moment,integrand,one_pow,sub_self,zero_pow (Nat.succ_ne_zero _),
    one_mul,zero_mul,sub_zero] using h

lemma moment_decomposition (m n : Nat) : moment m n=moment m (n+1)+moment (m+1) n := by
  unfold moment
  rw [←intervalIntegral.integral_add ((integrand_continuous m (n+1)).intervalIntegrable _ _)
    ((integrand_continuous (m+1) n).intervalIntegrable _ _)]
  congr 1
  funext x;unfold integrand;ring

lemma moment_step (m n : Nat) :
    ((m+n+2:Nat):ℝ)*moment m (n+1)=((n+1:Nat):ℝ)*moment m n := by
  have h:=moment_parts m n
  rw [moment_decomposition m n]
  push_cast at h ⊢;nlinarith

theorem lawsViaMathlib : ComputableAnalysis.BetaIntegral.Laws where
  base := by
    intro m
    apply MathlibComparison.Cartwright.small_of_tendsto_zero
    have h:=((samples_tendsto m 0).const_mul ((m+1:Nat):ℝ)).sub
      (tendsto_const_nhds (x:=(1:ℝ)))
    simpa only [moment_base,sub_self,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_one] using h
  step := by
    intro m n
    apply MathlibComparison.Cartwright.small_of_tendsto_zero
    have h:=((samples_tendsto m (n+1)).const_mul ((m+n+2:Nat):ℝ)).sub
      ((samples_tendsto m n).const_mul ((n+1:Nat):ℝ))
    have he : ((m+n+2:Nat):ℝ)*moment m (n+1)-((n+1:Nat):ℝ)*moment m n=0 := by rw [moment_step,sub_self]
    simpa only [ComputableAnalysis.BetaIntegral.stepResidual,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,he] using h

end MathlibComparison.BetaIntegral

namespace ComputableAnalysis.BetaIntegral

theorem evaluation_viaMathlib (m n : Nat) : Statement m n :=
  evaluation_of_laws MathlibComparison.BetaIntegral.lawsViaMathlib m n

theorem factorial_viaMathlib (m n : Nat) : FactorialStatement m n :=
  factorial_of_laws MathlibComparison.BetaIntegral.lawsViaMathlib m n

end ComputableAnalysis.BetaIntegral
