import MathlibComparison.IntervalModel
import ComputableAnalysis.MonotoneAverage

/-! The order-theoretic quadrature bridge. No antiderivative, FTC theorem or
moment evaluation is used here. -/
namespace MathlibComparison.RealDyadicAverages
open ComputableAnalysis ClosedArctanInverse Filter Topology

noncomputable def left (f : ℝ → ℝ) (a b : Rat) : Nat → ℝ
  | 0 => f a
  | n+1 => (left f a ((a+b)/2) n+left f ((a+b)/2) b n)/2
noncomputable def right (f : ℝ → ℝ) (a b : Rat) : Nat → ℝ
  | 0 => f b
  | n+1 => (right f a ((a+b)/2) n+right f ((a+b)/2) b n)/2

lemma gap (f : ℝ → ℝ) (a b : Rat) (n : Nat) :
    left f a b n-right f a b n=(meshRadius n:ℝ)*(f a-f b) := by
  induction n generalizing a b with
  | zero => simp [left,right,meshRadius]
  | succ n ih =>
    rw [left,right,show meshRadius (n+1)=meshRadius n/2 from by
      simp only [meshRadius,Rat.pow_succ,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev];exact Rat.mul_comm _ _]
    push_cast
    have h1:=ih a ((a+b)/2);have h2:=ih ((a+b)/2) b
    linarith

lemma rectangle_bounds (f : ℝ → ℝ) (hf : Continuous f)
    (hmono : AntitoneOn f (Set.Icc (0:ℝ) 1))
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a≤b) (n : Nat) :
    ((b-a:Rat):ℝ)*right f a b n ≤ (∫ x in (a:ℝ)..(b:ℝ),f x) ∧
      (∫ x in (a:ℝ)..(b:ℝ),f x) ≤ ((b-a:Rat):ℝ)*left f a b n := by
  have hA : (a:ℝ)∈Set.Icc (0:ℝ) 1 := by exact ⟨by exact_mod_cast ha.1,by exact_mod_cast ha.2⟩
  have hB : (b:ℝ)∈Set.Icc (0:ℝ) 1 := by exact ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2⟩
  have habR : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  induction n generalizing a b with
  | zero =>
    have hlo:=intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) habR
      (continuous_const.intervalIntegrable (a:ℝ) (b:ℝ)) (hf.intervalIntegrable (a:ℝ) (b:ℝ))
      (f:=fun _=>f b) (g:=f) (fun x hx=>hmono ⟨le_trans hA.1 hx.1,le_trans hx.2 hB.2⟩ hB hx.2)
    have hhi:=intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) habR
      (hf.intervalIntegrable (a:ℝ) (b:ℝ)) (continuous_const.intervalIntegrable (a:ℝ) (b:ℝ))
      (f:=f) (g:=fun _=>f a) (fun x hx=>hmono hA ⟨le_trans hA.1 hx.1,le_trans hx.2 hB.2⟩ hx.1)
    simpa [left,right,intervalIntegral.integral_const] using And.intro hlo hhi
  | succ n ih =>
    let m : Rat := (a+b)/2
    have hm : Unit m := MonotoneAverage.midpoint_unit ha hb
    have hbet:=MonotoneAverage.midpoint_between hab
    have hM : (m:ℝ)∈Set.Icc (0:ℝ) 1 := by exact ⟨by exact_mod_cast hm.1,by exact_mod_cast hm.2⟩
    have h1:=ih ha hm hbet.1 hA hM (by exact_mod_cast hbet.1)
    have h2:=ih hm hb hbet.2 hM hB (by exact_mod_cast hbet.2)
    have hadd:=intervalIntegral.integral_add_adjacent_intervals (μ:=MeasureTheory.volume)
      (hf.intervalIntegrable (a:ℝ) (m:ℝ)) (hf.intervalIntegrable (m:ℝ) (b:ℝ))
    have hma : ((m-a:Rat):ℝ)=((b-a:Rat):ℝ)/2 := by dsimp [m];push_cast;ring
    have hbm : ((b-m:Rat):ℝ)=((b-a:Rat):ℝ)/2 := by dsimp [m];push_cast;ring
    rw [hma] at h1
    rw [hbm] at h2
    rw [left,right]
    change ((b-a:Rat):ℝ)*((right f a m n+right f m b n)/2)≤_ ∧
      _≤((b-a:Rat):ℝ)*((left f a m n+left f m b n)/2)
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2,hadd]

lemma unit_error (f : ℝ → ℝ) (hf : Continuous f)
    (hmono : AntitoneOn f (Set.Icc (0:ℝ) 1)) (h0 : f 0≤1) (h1 : 0≤f 1) (n : Nat) :
    |left f 0 1 n-(∫ x in (0:ℝ)..1,f x)|≤(meshRadius n:ℝ) := by
  have h:=rectangle_bounds f hf hmono (a:=0) (b:=1)
    ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ (by decide) n
  have hg:=gap f 0 1 n
  norm_num only [Rat.cast_sub,Rat.cast_zero,Rat.cast_one,sub_zero,one_mul] at h hg
  have hp : (0:ℝ)≤(meshRadius n:ℝ) := by exact_mod_cast le_of_lt (meshRadius_pos n)
  have hmul:=mul_le_mul_of_nonneg_left (show f 0-f 1≤1 by linarith) hp
  rw [abs_of_nonneg (sub_nonneg.mpr h.2)]
  linarith

lemma samples_tendsto (sample : Rat → Nat → Rat) (f : ℝ → ℝ)
    (hs : ∀ x, Unit x → Tendsto (fun q=>(sample x q:ℝ)) atTop (𝓝 (f x)))
    {a b : Rat} (ha : Unit a) (hb : Unit b) (d : Nat) :
    Tendsto (fun q=>(MonotoneAverage.left (fun x=>sample x q) a b d:ℝ)) atTop (𝓝 (left f a b d)) := by
  induction d generalizing a b with
  | zero => exact hs a ha
  | succ d ih =>
    have h1:=ih ha (MonotoneAverage.midpoint_unit ha hb)
    have h2:=ih (MonotoneAverage.midpoint_unit ha hb) hb
    simpa only [MonotoneAverage.left,left,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat] using (h1.add h2).div_const 2

/-- The diagonal limit follows from a proved uniform mesh estimate and fixed-
mesh evaluation convergence. No arbitrary pointwise diagonal is assumed. -/
lemma diagonal_tendsto (sample : Rat → Nat → Rat) (f : ℝ → ℝ)
    (hs : ∀ x, Unit x → Tendsto (fun q=>(sample x q:ℝ)) atTop (𝓝 (f x)))
    (hf : Continuous f) (hm : AntitoneOn f (Set.Icc (0:ℝ) 1))
    (h0 : f 0≤1) (h1 : 0≤f 1)
    (mesh : ∀ d q, d≤q →
      qabs (MonotoneAverage.left (fun x=>sample x q) 0 1 q-
        MonotoneAverage.left (fun x=>sample x q) 0 1 d)≤meshRadius d) :
    Tendsto (fun q=>(MonotoneAverage.left (fun x=>sample x q) 0 1 q:ℝ)) atTop
      (𝓝 (∫ x in (0:ℝ)..1,f x)) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  obtain ⟨d,hd⟩ := exists_nat_gt ((4:ℝ)/eps)
  have hd' : (meshRadius d:ℝ)<eps/4 := by
    have hn : (meshRadius d:ℝ)≤1/((d+1:Nat):ℝ) := by
      have h := (Rat.cast_le (K:=ℝ)).2 (meshRadius_le d)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using h
    apply lt_of_le_of_lt hn
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<((d+1:Nat):ℝ))]
    have h := (div_lt_iff₀ heps).mp hd
    push_cast
    nlinarith
  have ht:=samples_tendsto sample f hs (a:=0) (b:=1) ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ d
  obtain ⟨N,hN⟩:=Metric.tendsto_atTop.1 ht (eps/2) (by positivity)
  refine ⟨max N d,fun q hq => ?_⟩
  have hE:=hN q (by omega)
  have hM : |(MonotoneAverage.left (fun x=>sample x q) 0 1 q:ℝ)-
      (MonotoneAverage.left (fun x=>sample x q) 0 1 d:ℝ)|≤(meshRadius d:ℝ) := by
    have hc : (qabs (MonotoneAverage.left (fun x=>sample x q) 0 1 q-
      MonotoneAverage.left (fun x=>sample x q) 0 1 d):ℝ)≤(meshRadius d:ℝ) := by exact_mod_cast mesh d q (by omega)
    simpa only [qabs_cast,Rat.cast_sub] using hc
  have hR:=unit_error f hf hm h0 h1 d
  rw [Real.dist_eq] at hE ⊢
  calc
    _ ≤ |(MonotoneAverage.left (fun x=>sample x q) 0 1 q:ℝ)-(MonotoneAverage.left (fun x=>sample x q) 0 1 d:ℝ)|+
        |(MonotoneAverage.left (fun x=>sample x q) 0 1 d:ℝ)-left f 0 1 d|+
        |left f 0 1 d-(∫ x in (0:ℝ)..1,f x)| := by
      exact (abs_sub_le _ _ _).trans (add_le_add_left (abs_sub_le _ _ _) _)
    _ < eps := by linarith

end MathlibComparison.RealDyadicAverages
