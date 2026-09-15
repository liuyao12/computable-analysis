import MathlibComparison.IntervalModel
import ComputableAnalysis.GeometricSineDerivative

/-! Compare the arctangent rectangle algorithm with Mathlib's independently
constructed arctangent. The proof is cellwise integral order, not either
native cosine integral proof. -/
namespace MathlibComparison
open ComputableAnalysis ArctanGeometry Filter Topology

private lemma kernel_continuous : Continuous (fun x : ℝ => (1+x^2)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro x
  positivity

private lemma kernel_antitone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (1+y^2)⁻¹ ≤ (1+x^2)⁻¹ := by
  apply inv_le_inv₀ (by positivity) (by positivity) |>.2
  nlinarith

lemma arctan_cell {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) :
    (integralLowerStep a b : ℝ) ≤ Real.arctan (b:ℝ)-Real.arctan (a:ℝ) ∧
    Real.arctan (b:ℝ)-Real.arctan (a:ℝ) ≤ (integralUpperStep a b : ℝ) := by
  have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
  have ha' : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hl := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab'
    (continuous_const.intervalIntegrable (a:ℝ) (b:ℝ))
    (kernel_continuous.intervalIntegrable (a:ℝ) (b:ℝ))
    (fun x hx => kernel_antitone (by linarith [hx.1]) hx.2)
  have hu := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab'
    (kernel_continuous.intervalIntegrable (a:ℝ) (b:ℝ))
    (continuous_const.intervalIntegrable (a:ℝ) (b:ℝ))
    (fun x hx => kernel_antitone ha' hx.1)
  rw [intervalIntegral.integral_const, integral_inv_one_add_sq] at hl
  rw [intervalIntegral.integral_const, integral_inv_one_add_sq] at hu
  unfold integralLowerStep integralUpperStep integralKernel
  push_cast
  simpa only [smul_eq_mul,one_div,pow_two] using And.intro hl hu

lemma arctan_cover {cells : List (Rat × Rat)} {a b : Rat}
    (ha : 0 ≤ a) (hc : CoversInterval a b cells) :
    (integralLowerSum cells : ℝ) ≤ Real.arctan (b:ℝ)-Real.arctan (a:ℝ) ∧
    Real.arctan (b:ℝ)-Real.arctan (a:ℝ) ≤ (integralUpperSum cells : ℝ) := by
  induction cells generalizing a with
  | nil =>
      have he : a=b := hc
      subst b
      simp [integralLowerSum,integralUpperSum]
  | cons cell cells ih =>
      rcases cell with ⟨p,r⟩
      rcases hc with ⟨rfl,hpr,hrest⟩
      have hcell := arctan_cell ha hpr
      have htail := ih (le_trans ha hpr) hrest
      simp only [integralLowerSum,integralUpperSum,Rat.cast_add]
      constructor <;> linarith

/-- Every box of the rational rectangle program contains Mathlib arctan. -/
lemma arctan_rectangle_represents {u : Rat} (hu : 0 ≤ u) :
    Represents (arctanIntegralRectangleRaw u) (Real.arctan (u:ℝ)) := by
  intro n
  have hh := arctan_cover (by decide : (0:Rat) ≤ 0)
    (arctanAreaLoopState_intervals_covers hu n)
  simpa only [arctanIntegralRectangleRaw,arctanIntegralRectangleCompute,integralSumInterval,
    Rat.cast_zero,Real.arctan_zero,sub_zero] using hh

lemma arctan_geom_represents {u : Rat} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Represents (arctanGeom u) (Real.arctan (u:ℝ)) :=
  represents_of_equiv (arctanIntegralRectangleRaw_valid hu0 hu1)
    (arctanGeom_valid_on_unit hu0 hu1) (arctanIntegralRectangleRaw_equiv_arctanGeom hu0)
    (arctan_rectangle_represents hu0)

/-- The native arctangent presentation of pi represents Mathlib's pi. -/
lemma four_arctan_one_represents :
    Represents ((4 : Nat) * arctanGeom 1) Real.pi := by
  have hh := represents_scale (4:Rat)
    (arctan_geom_represents (by decide : (0:Rat)≤1) (by decide : (1:Rat)≤1))
  norm_num only [Rat.cast_ofNat,Real.arctan_one] at hh
  convert hh using 1 <;> try { congr 1 }
  ring

lemma piCircleArea_represents : Represents piCircleArea Real.pi := by
  intro n
  have h := four_arctan_one_represents n
  rwa [four_arctanGeom_one_compute_eq_piCircleArea_compute] at h

lemma reciprocalPi_represents : Represents SinPiIntegral.reciprocalPiRaw Real.pi⁻¹ := by
  intro n
  have hp := piCircleArea_represents n
  have hnest := CauchyPi.piCircleArea_valid.2.1 0 n (Nat.zero_le n)
  have hzero : piCircleArea.compute 0 = ({lo:=2,hi:=4}:QInterval) := by decide +kernel
  rw [hzero] at hnest
  have hqlo : (0:Rat)<(piCircleArea.compute n).lo := by
    have hh := hnest.1
    dsimp at hh
    linarith
  have hlo : (0:ℝ)<((piCircleArea.compute n).lo:ℝ) := by exact_mod_cast hqlo
  change ((QInterval.inv (piCircleArea.compute n)).lo : ℝ) ≤ _ ∧
    _ ≤ ((QInterval.inv (piCircleArea.compute n)).hi : ℝ)
  simp only [QInterval.inv,if_pos hqlo,Rat.cast_div,Rat.cast_one]
  constructor
  · simpa only [one_div] using one_div_le_one_div_of_le Real.pi_pos hp.2
  · simpa only [one_div] using one_div_le_one_div_of_le hlo hp.1

end MathlibComparison
