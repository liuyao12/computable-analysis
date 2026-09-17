import MathlibComparison.TrigonometryBridge
import MathlibComparison.RealDyadicAverages
import MathlibComparison.CartwrightRealMoments
import ComputableAnalysis.CartwrightIrrationality

/-! The comparison route for the SAME native weighted-moment computations.
The quadrature bridge uses integral order and finite additivity, not the
moment recurrence. The Mathlib recurrence supplies precisely the laws used
by the shared finite algebra and integer contradiction. -/
namespace MathlibComparison.Cartwright
open ComputableAnalysis ClosedArctanInverse Filter Topology IntervalSelections

lemma clock_cosine_represents (x : Rat) (hx : Unit x) :
    Represents (ClockTrigonometry.cosine x) (Real.cos (lambda*(x:ℝ))) := by
  have hhalf : GeometricSineDerivative.OnHalf (x/2) := by
    have h0:=hx.1;have h1:=hx.2
    change 0≤x/2 ∧ x/2≤(1:Rat)/2
    constructor <;> linarith
  have hc:=cosine_represents ClosedArctanInverse.provider (x/2) hhalf
  change Represents (ClockTrigonometry.cosine (2*(x/2))) (Real.cos (Real.pi*((x/2:Rat):ℝ))) at hc
  rw [show (2:Rat)*(x/2)=x by ring] at hc
  have he : Real.pi*((x/2:Rat):ℝ)=lambda*(x:ℝ) := by
    push_cast;unfold lambda;ring
  rw [he] at hc
  exact hc

lemma cosine_samples_tendsto (x : Rat) (hx : Unit x) :
    Tendsto (fun q=>(ClockTrigonometry.c x q:ℝ)) atTop (𝓝 (Real.cos (lambda*(x:ℝ)))) :=
  selected_tendsto (ClockTrigonometry.cosine_valid hx) (clock_cosine_represents x hx)
    (ClockTrigonometry.c x) (ClockTrigonometry.c_mem hx)

lemma weighted_samples_tendsto (n : Nat) (x : Rat) (hx : Unit x) :
    Tendsto (fun q=>(ComputableAnalysis.CartwrightMoments.sample n x q:ℝ)) atTop
      (𝓝 ((1-(x:ℝ)^2)^n*Real.cos (lambda*(x:ℝ)))) := by
  have h:= (cosine_samples_tendsto x hx).const_mul ((1-(x:ℝ)^2)^n)
  simpa only [ComputableAnalysis.CartwrightMoments.sample,ComputableAnalysis.CartwrightMoments.weight,Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_one,pow_two] using h

lemma cosine_nonnegative {x : ℝ} (hx : x∈Set.Icc (0:ℝ) 1) :
    0≤Real.cos (lambda*x) := by
  apply Real.cos_nonneg_of_mem_Icc
  have hp:=lambda_pos
  constructor
  · nlinarith [hx.1,Real.pi_pos]
  · unfold lambda;nlinarith [hx.2,Real.pi_pos]

lemma moment_integrand_antitone (n : Nat) :
    AntitoneOn (fun x:ℝ=>(1-x^2)^n*Real.cos (lambda*x)) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : 0≤1-x^2 := by nlinarith [hx.1,hx.2]
  have hy0 : 0≤1-y^2 := by nlinarith [hy.1,hy.2]
  have hxyw : 1-y^2≤1-x^2 := by nlinarith [hx.1,hy.1]
  have hw : (1-y^2)^n≤(1-x^2)^n := pow_le_pow_left₀ hy0 hxyw n
  have hc : Real.cos (lambda*y)≤Real.cos (lambda*x) :=
    Real.cos_le_cos_of_nonneg_of_le_pi
      (mul_nonneg (le_of_lt lambda_pos) hx.1)
      (by unfold lambda;nlinarith [hy.2,Real.pi_pos])
      (mul_le_mul_of_nonneg_left hxy (le_of_lt lambda_pos))
  exact mul_le_mul hw hc (cosine_nonnegative hy) (pow_nonneg hx0 n)

lemma moment_samples_tendsto (n : Nat) :
    Tendsto (fun q=>(ComputableAnalysis.CartwrightMoments.momentSample n q:ℝ)) atTop (𝓝 (moment n)) := by
  apply RealDyadicAverages.diagonal_tendsto (ComputableAnalysis.CartwrightMoments.sample n)
    (fun x:ℝ=>(1-x^2)^n*Real.cos (lambda*x)) (weighted_samples_tendsto n)
    (moment_continuous n) (moment_integrand_antitone n) (by simp) (by simp [cos_lambda])
  intro d q hdq
  have h:=MonotoneAverage.mesh_error (fun x=>ComputableAnalysis.CartwrightMoments.sample n x q) (ComputableAnalysis.CartwrightMoments.sample_decreases n q)
    (ComputableAnalysis.CartwrightMoments.sample_unit n (x:=1) ⟨by decide,by decide⟩ q).1
    (ComputableAnalysis.CartwrightMoments.sample_unit n (x:=0) ⟨by decide,by decide⟩ q).2 hdq
  rw [show MonotoneAverage.left (fun x=>ComputableAnalysis.CartwrightMoments.sample n x q) 0 1 q-
      MonotoneAverage.left (fun x=>ComputableAnalysis.CartwrightMoments.sample n x q) 0 1 d =
      -(MonotoneAverage.left (fun x=>ComputableAnalysis.CartwrightMoments.sample n x q) 0 1 d-
        MonotoneAverage.left (fun x=>ComputableAnalysis.CartwrightMoments.sample n x q) 0 1 q) by ring,qabs_neg]
  exact h

/-- Identification of the actual native quadrature, before its evaluation. -/
theorem moment_represents (n : Nat) : Represents (ComputableAnalysis.CartwrightMoments.moment n) (moment n) :=
  represents_of_tendsto (ComputableAnalysis.CartwrightMoments.moment_valid n) (ComputableAnalysis.CartwrightMoments.momentSample n) (ComputableAnalysis.CartwrightMoments.momentSample_mem n) (moment_samples_tendsto n)

lemma frequency_samples_tendsto :
    Tendsto (fun q=>(ComputableAnalysis.CartwrightMoments.frequencySample q:ℝ)) atTop (𝓝 lambda) := by
  have h:=lower_tendsto CauchyPi.piCircleArea_valid piCircleArea_represents
  simpa only [ComputableAnalysis.CartwrightMoments.frequencySample,Rat.cast_div,Rat.cast_ofNat,lambda] using h.div_const 2

lemma small_of_tendsto_zero (e : Nat → Rat)
    (he : Tendsto (fun q=>(e q:ℝ)) atTop (𝓝 0)) : ComputableAnalysis.RationalSampleLimits.Small e := by
  intro eps
  have hp : (0:ℝ)<(eps.val:ℝ) := by exact_mod_cast eps.property
  obtain ⟨N,hN⟩:=Metric.tendsto_atTop.1 he (eps.val:ℝ) hp
  refine ⟨N,fun q hq => ?_⟩
  have h:=hN q hq
  rw [Real.dist_eq,sub_zero] at h
  have hcast : (qabs (e q):ℝ)≤(eps.val:ℝ) := by rw [qabs_cast];exact le_of_lt h
  exact_mod_cast hcast

/-- A closed comparison certificate; no native moment evaluation is used. -/
theorem lawsViaMathlib : ComputableAnalysis.CartwrightMoments.MomentLaws where
  zero := by
    apply small_of_tendsto_zero
    have ht:=(frequency_samples_tendsto.mul (moment_samples_tendsto 0)).sub
      (tendsto_const_nhds (x:=(1:ℝ)))
    have he : lambda*moment 0-1=0 := by rw [moment_zero];ring
    simpa only [Rat.cast_sub,Rat.cast_mul,Rat.cast_one,he] using ht
  first := by
    apply small_of_tendsto_zero
    have ht:=((frequency_samples_tendsto.mul frequency_samples_tendsto).mul (moment_samples_tendsto 1)).sub
      ((moment_samples_tendsto 0).const_mul 2)
    have he : lambda*lambda*moment 1-2*moment 0=0 := by nlinarith only [moment_one]
    simpa only [ComputableAnalysis.CartwrightMoments.firstSamples,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,he] using ht
  recurrence := by
    intro n
    apply small_of_tendsto_zero
    have ht:=(((frequency_samples_tendsto.mul frequency_samples_tendsto).mul (moment_samples_tendsto (n+2))).sub
      ((moment_samples_tendsto (n+1)).const_mul (ComputableAnalysis.CartwrightMoments.recurrenceA n:ℝ))).add
      ((moment_samples_tendsto n).const_mul (ComputableAnalysis.CartwrightMoments.recurrenceB n:ℝ))
    have hA : (ComputableAnalysis.CartwrightMoments.recurrenceA n:ℝ)=2*(n+2:ℝ)*(2*n+3) := by simp [ComputableAnalysis.CartwrightMoments.recurrenceA]
    have hB : (ComputableAnalysis.CartwrightMoments.recurrenceB n:ℝ)=4*(n+2:ℝ)*(n+1) := by simp [ComputableAnalysis.CartwrightMoments.recurrenceB]
    have he : lambda*lambda*moment (n+2)-(ComputableAnalysis.CartwrightMoments.recurrenceA n:ℝ)*moment (n+1)+(ComputableAnalysis.CartwrightMoments.recurrenceB n:ℝ)*moment n=0 := by
      rw [hA,hB];nlinarith only [moment_recurrence n]
    simpa only [ComputableAnalysis.CartwrightMoments.recurrenceSamples,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,he] using ht

end MathlibComparison.Cartwright

namespace ComputableAnalysis.CartwrightMoments

theorem evaluation_viaMathlib (n : Nat) : EvaluationStatement n :=
  evaluation_of_laws MathlibComparison.Cartwright.lawsViaMathlib n

theorem piSquared_viaMathlib : PiSquaredStatement :=
  piSquared_of_laws MathlibComparison.Cartwright.lawsViaMathlib

end ComputableAnalysis.CartwrightMoments
