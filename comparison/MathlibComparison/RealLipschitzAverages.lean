import MathlibComparison.RealDyadicAverages
import ComputableAnalysis.RationalLipschitzIntegral

/-! A quadrature correspondence from cellwise inequalities. No primitive
or integral evaluation is used in this bridge. -/
namespace MathlibComparison.RealLipschitzAverages
open ComputableAnalysis ClosedArctanInverse Filter Topology
open RealDyadicAverages

lemma rectangle_error (f : ℝ → ℝ) (hf : Continuous f) (L : ℝ) (hL : 0≤L)
    (lip : ∀ x y, x∈Set.Icc (0:ℝ) 1 → y∈Set.Icc (0:ℝ) 1 → |f x-f y|≤L*|x-y|)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a≤b) (d : Nat) :
    |((b-a:Rat):ℝ)*left f a b d-(∫ x in (a:ℝ)..(b:ℝ),f x)|≤
      L*((b-a:Rat):ℝ)^2*(meshRadius d:ℝ) := by
  have haR : (a:ℝ)∈Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast ha.1,by exact_mod_cast ha.2⟩
  have hbR : (b:ℝ)∈Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2⟩
  have habR : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  induction d generalizing a b with
  | zero =>
    have bound (x : ℝ) (hx : x∈Set.Icc (a:ℝ) (b:ℝ)) :
        f a-L*((b:ℝ)-a)≤f x ∧ f x≤f a+L*((b:ℝ)-a) := by
      have h:=lip x a ⟨le_trans haR.1 hx.1,le_trans hx.2 hbR.2⟩ haR
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at h
      have hh:=abs_le.mp h
      constructor <;> nlinarith [hx.2]
    have lo:=intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) habR
      (continuous_const.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
      (f:=fun _=>f a-L*((b:ℝ)-a)) (g:=f) (fun x hx=>(bound x hx).1)
    have hi:=intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) habR
      (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (f:=f) (g:=fun _=>f a+L*((b:ℝ)-a)) (fun x hx=>(bound x hx).2)
    simp only [left, show meshRadius 0 = 1 by decide +kernel, Rat.cast_one, mul_one, Rat.cast_sub]
    rw [intervalIntegral.integral_const] at lo hi
    simp only [smul_eq_mul] at lo hi
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  | succ d ih =>
    let m : Rat := (a+b)/2
    have hm:=MonotoneAverage.midpoint_unit ha hb
    have between:=MonotoneAverage.midpoint_between hab
    have hmR : (m:ℝ)∈Set.Icc (0:ℝ) 1 := ⟨by exact_mod_cast hm.1,by exact_mod_cast hm.2⟩
    have h1:=ih ha hm between.1 haR hmR (by exact_mod_cast between.1)
    have h2:=ih hm hb between.2 hmR hbR (by exact_mod_cast between.2)
    have hadd:=intervalIntegral.integral_add_adjacent_intervals (μ:=MeasureTheory.volume)
      (hf.intervalIntegrable (a:ℝ) (m:ℝ)) (hf.intervalIntegrable (m:ℝ) (b:ℝ))
    have hma : ((m-a:Rat):ℝ)=((b-a:Rat):ℝ)/2 := by dsimp [m];push_cast;ring
    have hbm : ((b-m:Rat):ℝ)=((b-a:Rat):ℝ)/2 := by dsimp [m];push_cast;ring
    have hr : meshRadius (d+1)=meshRadius d/2 := by
      simp only [meshRadius,Rat.pow_succ,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev];exact Rat.mul_comm _ _
    have ht:=abs_add_le
      (((m-a:Rat):ℝ)*left f a m d-(∫ x in (a:ℝ)..(m:ℝ),f x))
      (((b-m:Rat):ℝ)*left f m b d-(∫ x in (m:ℝ)..(b:ℝ),f x))
    rw [hma] at h1 ht;rw [hbm] at h2 ht
    rw [left,hr]
    change |((b-a:Rat):ℝ)*((left f a m d+left f m b d)/2)-_|≤_
    rw [Rat.cast_div, Rat.cast_ofNat]
    have he : ((b-a:Rat):ℝ)/2*left f a m d-(∫ x in (a:ℝ)..(m:ℝ),f x)+
      (((b-a:Rat):ℝ)/2*left f m b d-(∫ x in (m:ℝ)..(b:ℝ),f x)) =
      ((b-a:Rat):ℝ)*((left f a m d+left f m b d)/2)-(∫ x in (a:ℝ)..(b:ℝ),f x) := by
      rw [←hadd];ring
    rw [he] at ht
    calc
      _ ≤ _ := ht
      _ ≤ L*(((b-a:Rat):ℝ)/2)^2*(meshRadius d:ℝ)+L*(((b-a:Rat):ℝ)/2)^2*(meshRadius d:ℝ) := add_le_add h1 h2
      _ = _ := by push_cast;ring

lemma left_cast (f : Rat → Rat) (g : ℝ → ℝ) (agree : ∀ x, (f x:ℝ)=g x)
    (a b : Rat) (d : Nat) : (MonotoneAverage.left f a b d:ℝ)=left g a b d := by
  induction d generalizing a b with
  | zero => exact agree a
  | succ d ih => simp only [MonotoneAverage.left,left,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,ih]

lemma samples_tendsto (D : RationalLipschitzIntegral.Data) (f : ℝ → ℝ)
    (agree : ∀ x, (D.sample x:ℝ)=f x) (hf : Continuous f)
    (lip : ∀ x y, x∈Set.Icc (0:ℝ) 1 → y∈Set.Icc (0:ℝ) 1 → |f x-f y|≤(D.constant:ℝ)*|x-y|) :
    Tendsto (fun q=>(RationalLipschitzIntegral.centre D q:ℝ)) atTop
      (𝓝 (∫ x in (0:ℝ)..1,f x)) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨N,hN⟩:=exists_nat_gt ((D.constant:ℝ)/eps)
  refine ⟨N,fun q hq=>?_⟩
  have h:=rectangle_error f hf D.constant (Nat.cast_nonneg _) lip
    (a:=0) (b:=1) ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide) q
  norm_num only [Rat.cast_sub,Rat.cast_zero,Rat.cast_one,sub_zero,one_mul,one_pow,mul_one] at h
  have hm : (meshRadius q:ℝ)≤1/((q+1:Nat):ℝ) := by
    have hh:=(Rat.cast_le (K:=ℝ)).2 (meshRadius_le q)
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using hh
  have hsmall : (D.constant:ℝ)*(meshRadius q:ℝ)<eps := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _))
    rw [mul_one_div,div_lt_iff₀ (by positivity : (0:ℝ)<((q+1:Nat):ℝ))]
    have hr : (N:ℝ)≤q := by exact_mod_cast hq
    have hn := (div_lt_iff₀ heps).mp hN
    push_cast;nlinarith
  rw [Real.dist_eq]
  change |(MonotoneAverage.left D.sample 0 1 q:ℝ)-_|<eps
  rw [left_cast D.sample f agree]
  exact lt_of_le_of_lt h hsmall

/-- This is independent of any proposed value of the integral. -/
theorem represents (D : RationalLipschitzIntegral.Data) (f : ℝ → ℝ)
    (agree : ∀ x, (D.sample x:ℝ)=f x) (hf : Continuous f)
    (lip : ∀ x y, x∈Set.Icc (0:ℝ) 1 → y∈Set.Icc (0:ℝ) 1 → |f x-f y|≤(D.constant:ℝ)*|x-y|) :
    Represents (RationalLipschitzIntegral.raw D) (∫ x in (0:ℝ)..1,f x) :=
  represents_of_tendsto (RationalLipschitzIntegral.valid D) (RationalLipschitzIntegral.centre D)
    (fun q=>RationalLipschitzIntegral.contains_future D q q (Nat.le_refl q))
    (samples_tendsto D f agree hf lip)

end MathlibComparison.RealLipschitzAverages
