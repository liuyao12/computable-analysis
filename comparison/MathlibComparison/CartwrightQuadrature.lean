import MathlibComparison.TrigonometryBridge
import MathlibComparison.CartwrightAnalytic
import ComputableAnalysis.CartwrightIntegrationByParts

/-! The actual native monotone moment quadrature represents Mathlib's integral.
Only value bridges, monotonicity, integral order and finite additivity are used;
no moment evaluation, integration-by-parts theorem, or irrationality theorem is
used in establishing this correspondence. -/
namespace MathlibComparison.CartwrightQuadrature
open ComputableAnalysis CartwrightMoments IntervalSelections Filter Topology
namespace R
noncomputable section
abbrev weight := CartwrightAnalytic.weight
abbrev c := CartwrightAnalytic.c
abbrev frequency := CartwrightAnalytic.frequency
abbrev moment := CartwrightAnalytic.moment
end
end R

lemma frequency_represents : Represents CartwrightClockBounds.frequency R.frequency := by
  have h:=represents_scale (2:Rat) (arctan_rectangle_represents (u:=1) (by decide +kernel))
  norm_num only [Rat.cast_ofNat,Rat.cast_one,Real.arctan_one] at h
  convert! h using 1
  unfold R.frequency CartwrightAnalytic.frequency
  ring

lemma cosine_represents {x : Rat} (hx : CartwrightMoments.Unit x) :
    Represents (ClockTrigonometry.cosine x) (R.c (x:ℝ)) := by
  have hh : GeometricSineDerivative.OnHalf (x/2) := by
    change 0≤x/2 ∧ x/2≤(1:Rat)/2
    constructor <;> linarith [hx.1,hx.2]
  have h:=MathlibComparison.cosine_represents ClosedArctanInverse.provider (x/2) hh
  change Represents (ClockTrigonometry.cosine (2*(x/2))) _ at h
  rw [show (2:Rat)*(x/2)=x by ring] at h
  convert! h using 1
  unfold R.c CartwrightAnalytic.c CartwrightAnalytic.frequency
  push_cast
  congr 1
  ring

lemma value_represents {x : Rat} (hx : CartwrightMoments.Unit x) (n : Nat) :
    Represents (CartwrightMoments.value n x) (R.weight n (x:ℝ)*R.c (x:ℝ)) := by
  have h:=represents_scale (CartwrightMoments.weight n x) (cosine_represents hx)
  simpa only [CartwrightMoments.value,CartwrightMoments.weight,R.weight,CartwrightAnalytic.weight,
    Rat.cast_pow,Rat.cast_sub,Rat.cast_one,Rat.cast_mul] using h

lemma continuous_integrand (n : Nat) : Continuous (fun x=>R.weight n x*R.c x) :=
  (CartwrightAnalytic.continuous_weight n).mul CartwrightAnalytic.continuous_c

lemma integrand_antitone (n : Nat) {a b : ℝ} (ha : a∈Set.Icc (0:ℝ) 1)
    (hb : b∈Set.Icc (0:ℝ) 1) (hab : a≤b) :
    R.weight n b*R.c b≤R.weight n a*R.c a := by
  have hf : 0<R.frequency := by unfold R.frequency CartwrightAnalytic.frequency;positivity
  have hA : R.frequency*a∈Set.Icc (0:ℝ) Real.pi := by
    unfold R.frequency CartwrightAnalytic.frequency
    constructor <;> nlinarith [Real.pi_pos,ha.1,ha.2]
  have hB : R.frequency*b∈Set.Icc (0:ℝ) Real.pi := by
    unfold R.frequency CartwrightAnalytic.frequency
    constructor <;> nlinarith [Real.pi_pos,hb.1,hb.2]
  have hcos : R.c b≤R.c a :=
    Real.antitoneOn_cos hA hB (mul_le_mul_of_nonneg_left hab (le_of_lt hf))
  have hc0 : 0≤R.c b := by
    apply Real.cos_nonneg_of_mem_Icc
    unfold CartwrightAnalytic.frequency
    constructor <;> nlinarith [Real.pi_pos,hb.1,hb.2]
  have hwa : 0≤R.weight n a := by
    apply pow_nonneg
    nlinarith [ha.1,ha.2]
  have hw : R.weight n b≤R.weight n a := by
    apply pow_le_pow_left₀
    · nlinarith [hb.1,hb.2]
    · nlinarith [ha.1,hb.1,hab]
  exact mul_le_mul hw hcos hc0 hwa

private def lower (n k j : Nat) : Rat := ((CartwrightMoments.value n (grid k (j+1))).compute (sampleStage k)).lo
private def upper (n k j : Nat) : Rat := ((CartwrightMoments.value n (grid k j)).compute (sampleStage k)).hi

private lemma cell_bounds (n k j : Nat) (hj : j<cells k) :
    (step k:ℝ)*(lower n k j:ℝ)≤∫x in (grid k j:ℝ)..(grid k (j+1):ℝ),R.weight n x*R.c x ∧
    (∫x in (grid k j:ℝ)..(grid k (j+1):ℝ),R.weight n x*R.c x)≤(step k:ℝ)*(upper n k j:ℝ) := by
  have ha:=grid_unit k j (by omega);have hb:=grid_unit k (j+1) (by omega)
  have haR : (grid k j:ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> exact_mod_cast (by first | exact ha.1 | exact ha.2)
  have hbR : (grid k (j+1):ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> exact_mod_cast (by first | exact hb.1 | exact hb.2)
  have hstep : (grid k (j+1):ℝ)-(grid k j:ℝ)=(step k:ℝ) := by exact_mod_cast grid_step k j
  have hp : (0:ℝ)≤(step k:ℝ) := by exact_mod_cast (le_of_lt (step_pos k))
  have hab : (grid k j:ℝ)≤(grid k (j+1):ℝ) := by linarith
  have hl:= (value_represents hb n (sampleStage k)).1
  have hu:= (value_represents ha n (sampleStage k)).2
  have hlow : ∀x∈Set.Icc (grid k j:ℝ) (grid k (j+1):ℝ), (lower n k j:ℝ)≤R.weight n x*R.c x := by
    intro x hx
    have hxU : x∈Set.Icc (0:ℝ) 1 := ⟨le_trans haR.1 hx.1,le_trans hx.2 hbR.2⟩
    exact le_trans hl (integrand_antitone n hxU hbR hx.2)
  have hupp : ∀x∈Set.Icc (grid k j:ℝ) (grid k (j+1):ℝ), R.weight n x*R.c x≤(upper n k j:ℝ) := by
    intro x hx
    have hxU : x∈Set.Icc (0:ℝ) 1 := ⟨le_trans haR.1 hx.1,le_trans hx.2 hbR.2⟩
    exact le_trans (integrand_antitone n haR hxU hx.1) hu
  have hL:=intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) hab
    (continuous_const.intervalIntegrable _ _) ((continuous_integrand n).intervalIntegrable _ _) hlow
  have hU:=intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) hab
    ((continuous_integrand n).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hupp
  rw [intervalIntegral.integral_const] at hL hU
  simp only [smul_eq_mul,hstep] at hL hU
  exact ⟨hL,hU⟩

private lemma prefix_bounds (n k j : Nat) (hj : j≤cells k) :
    ((FiniteRiemannAlgebra.sum (fun i=>step k*lower n k i) j:Rat):ℝ)≤
      ∫x in (0:ℝ)..(grid k j:ℝ),R.weight n x*R.c x ∧
    (∫x in (0:ℝ)..(grid k j:ℝ),R.weight n x*R.c x)≤
      ((FiniteRiemannAlgebra.sum (fun i=>step k*upper n k i) j:Rat):ℝ) := by
  induction j with
  | zero => simp only [FiniteRiemannAlgebra.sum_zero,grid_zero,Rat.cast_zero,intervalIntegral.integral_same];exact ⟨le_rfl,le_rfl⟩
  | succ j ih =>
    have hprev:=ih (by omega)
    have hcell:=cell_bounds n k j (by omega)
    have hadd:=intervalIntegral.integral_add_adjacent_intervals (μ:=MeasureTheory.volume)
      ((continuous_integrand n).intervalIntegrable (0:ℝ) (grid k j:ℝ))
      ((continuous_integrand n).intervalIntegrable (grid k j:ℝ) (grid k (j+1):ℝ))
    rw [←hadd]
    simp only [FiniteRiemannAlgebra.sum_succ,Rat.cast_add,Rat.cast_mul]
    constructor <;> linarith

/-- Every native output box contains the same Mathlib moment. Its proof does
not use the recurrence or a cosine primitive formula. -/
theorem moment_represents (n : Nat) : Represents (CartwrightMoments.integral n) (R.moment n) := by
  intro k
  rw [integral_compute]
  have h:=prefix_bounds n k (cells k) (Nat.le_refl _)
  rw [grid_last,Rat.cast_one] at h
  exact h

theorem sample_tendsto (n : Nat) :
    Tendsto (fun k=>(CartwrightMoments.sample n k:ℝ)) atTop (𝓝 (R.moment n)) :=
  selected_tendsto (CartwrightMoments.integral_valid n) (moment_represents n)
    (CartwrightMoments.sample n) (CartwrightMoments.sample_mem n)

theorem frequency_tendsto :
    Tendsto (fun k=>(CartwrightIntegrationByParts.frequencySample k:ℝ)) atTop (𝓝 R.frequency) :=
  selected_tendsto CartwrightClockBounds.frequency_valid frequency_represents
    CartwrightIntegrationByParts.frequencySample CartwrightIntegrationByParts.frequencySample_mem

end MathlibComparison.CartwrightQuadrature
