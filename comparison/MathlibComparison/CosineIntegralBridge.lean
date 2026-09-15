import MathlibComparison.TrigonometryBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import ComputableAnalysis.CosineIntegralData

/-!
# From the native cosine quadrature to Mathlib's interval integral

The bridge uses only the pointwise cosine representation, a Lipschitz bound,
cellwise integral order, and finite additivity. It does not use an antiderivative
formula or either native cosine integral endpoint proof.
-/
namespace MathlibComparison
open ComputableAnalysis IntegralIdentities SinPiIntegral GeometricSineDerivative
open CosineFTC

/-- The independently defined Mathlib comparison integrand. -/
noncomputable def normalizedCosine (x : ℝ) : ℝ := Real.cos (Real.pi*x)

lemma normalizedCosine_continuous : Continuous normalizedCosine := by
  unfold normalizedCosine
  fun_prop

lemma normalizedCosine_lipschitz (x y : ℝ) :
    |normalizedCosine x-normalizedCosine y| ≤ 4*|x-y| := by
  have h := Real.abs_cos_sub_cos_le (Real.pi*x) (Real.pi*y)
  rw [← mul_sub,abs_mul,abs_of_pos Real.pi_pos] at h
  exact h.trans (mul_le_mul_of_nonneg_right Real.pi_le_four (abs_nonneg _))

/-- A finite-cell error estimate using integral order, not a primitive. -/
lemma cosine_cell_error {a b : ℝ} (hab : a ≤ b) :
    |(∫ x in a..b, normalizedCosine x)-(b-a)*normalizedCosine a| ≤ 4*(b-a)^2 := by
  have hlip (x : ℝ) (hx : x ∈ Set.Icc a b) :
      normalizedCosine a-4*(b-a) ≤ normalizedCosine x ∧
      normalizedCosine x ≤ normalizedCosine a+4*(b-a) := by
    have h := normalizedCosine_lipschitz x a
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at h
    have h1 := (abs_le.mp h).1
    have h2 := (abs_le.mp h).2
    constructor <;> linarith [hx.2]
  have hl := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (continuous_const.intervalIntegrable a b)
    (normalizedCosine_continuous.intervalIntegrable a b) (fun x hx => (hlip x hx).1)
  have hu := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (normalizedCosine_continuous.intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b) (fun x hx => (hlip x hx).2)
  rw [intervalIntegral.integral_const] at hl hu
  simp only [smul_eq_mul] at hl hu
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- Exact real-valued counterpart of one finite list of native rectangles. -/
noncomputable def rectangleValue (a b : Rat) (m k : Nat) : ℝ :=
  ((List.range k).map (fun i => (mesh a b m : ℝ)*
    normalizedCosine (leftPoint a b m i : ℝ))).sum

lemma rectangleValue_succ (a b : Rat) (m k : Nat) :
    rectangleValue a b m (k+1) = rectangleValue a b m k +
      (mesh a b m : ℝ)*normalizedCosine (leftPoint a b m k : ℝ) := by
  simp [rectangleValue,List.range_succ,List.map_append,List.sum_append]

/-- The finite rectangle error accumulates linearly in the number of cells. -/
lemma rectangle_error (a b : Rat) (hab : a ≤ b) (m : Nat) (hm : 0 < m) (k : Nat) :
    |(∫ x in (a : ℝ)..(leftPoint a b m k : ℝ), normalizedCosine x)-
      rectangleValue a b m k| ≤ (k : ℝ)*4*(mesh a b m : ℝ)^2 := by
  induction k with
  | zero => simp [rectangleValue,leftPoint_zero]
  | succ k ih =>
    have hh : (0 : ℝ) ≤ (mesh a b m : ℝ) := by
      exact_mod_cast mesh_nonneg_of_le hm hab
    have hs : (leftPoint a b m (k+1) : ℝ)-(leftPoint a b m k : ℝ) =
        (mesh a b m : ℝ) := by exact_mod_cast leftPoint_step a b m k
    have hcell := cosine_cell_error (a := (leftPoint a b m k : ℝ))
      (b := (leftPoint a b m (k+1) : ℝ)) (by linarith)
    rw [hs] at hcell
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (normalizedCosine_continuous.intervalIntegrable (a:ℝ) (leftPoint a b m k : ℝ))
      (normalizedCosine_continuous.intervalIntegrable (leftPoint a b m k : ℝ)
        (leftPoint a b m (k+1) : ℝ))
    rw [← hadd,rectangleValue_succ]
    have he : (∫ x in (a:ℝ)..(leftPoint a b m k:ℝ), normalizedCosine x) +
        (∫ x in (leftPoint a b m k:ℝ)..(leftPoint a b m (k+1):ℝ), normalizedCosine x) -
        (rectangleValue a b m k + (mesh a b m:ℝ)*normalizedCosine (leftPoint a b m k:ℝ)) =
      ((∫ x in (a:ℝ)..(leftPoint a b m k:ℝ), normalizedCosine x)-rectangleValue a b m k) +
      ((∫ x in (leftPoint a b m k:ℝ)..(leftPoint a b m (k+1):ℝ), normalizedCosine x)-
        (mesh a b m:ℝ)*normalizedCosine (leftPoint a b m k:ℝ)) := by ring
    rw [he]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ (k:ℝ)*4*(mesh a b m:ℝ)^2+4*(mesh a b m:ℝ)^2 := add_le_add ih hcell
      _ = ((k+1:Nat):ℝ)*4*(mesh a b m:ℝ)^2 := by push_cast; ring

lemma finiteRawSum_represents {ι : Type} (items : List ι)
    (X : ι → RealRaw) (v : ι → ℝ)
    (h : ∀ i ∈ items, Represents (X i) (v i)) :
    Represents (Integral.finiteRawSum (items.map X)) ((items.map v).sum) := by
  induction items with
  | nil => simpa only [List.map_nil,List.sum_nil,Integral.finiteRawSum,RealRaw.zero,Rat.cast_zero] using represents_rat (0:Rat)
  | cons i items ih =>
    exact represents_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- Every finite-stage native sum contains the corresponding exact real sum. -/
lemma fixedMesh_represents (B : ArctanInverseBisection) {a b : Rat}
    (ha : OnHalf a) (hb : OnHalf b) (hab : a ≤ b) (k : Nat) :
    Represents (fixedMesh B a b k) (rectangleValue a b (k+1) (k+1)) := by
  apply finiteRawSum_represents
  intro i hi
  have hx := grid_onHalf ha hb hab (Nat.succ_pos k) (Nat.le_of_lt (List.mem_range.mp hi))
  apply represents_scale
  have hc := cosine_represents B (leftPoint a b (k+1) i) hx
  simpa only [cosine,dif_pos hx,normalizedCosine] using hc

/-- A widened native mesh box contains the Mathlib interval integral at
EVERY evaluation stage; no diagonal convergence assumption is used. -/
lemma fixedMesh_contains_integral (B : ArctanInverseBisection) {a b : Rat}
    (ha : OnHalf a) (hb : OnHalf b) (hab : a ≤ b) (k n : Nat) :
    ((QInterval.expand ((fixedMesh B a b k).compute n) (error a b k)).lo : ℝ) ≤
      (∫ x in (a:ℝ)..(b:ℝ), normalizedCosine x) ∧
    (∫ x in (a:ℝ)..(b:ℝ), normalizedCosine x) ≤
      ((QInterval.expand ((fixedMesh B a b k).compute n) (error a b k)).hi : ℝ) := by
  have hr := fixedMesh_represents B ha hb hab k n
  have he := rectangle_error a b hab (k+1) (Nat.succ_pos k) (k+1)
  rw [leftPoint_endpoint (Nat.succ_pos k)] at he
  have hbudget : ((k+1:Nat):ℝ)*4*(mesh a b (k+1):ℝ)^2 ≤ (error a b k : ℝ) := by
    rw [error_eq_mesh]
    push_cast
    nlinarith [sq_nonneg (mesh a b (k+1):ℝ)]
  have herror := abs_le.mp (he.trans hbudget)
  simp only [QInterval.expand,Rat.cast_sub,Rat.cast_add]
  constructor <;> linarith

lemma intersect_contains_real {boxes : Nat → Nat → QInterval} {r : ℝ}
    (q k : Nat) (h : ∀ i ≤ k, ((boxes i q).lo : ℝ) ≤ r ∧ r ≤ ((boxes i q).hi : ℝ)) :
    ((Integral.Dovetail.intersectMeshes boxes q k).lo : ℝ) ≤ r ∧
    r ≤ ((Integral.Dovetail.intersectMeshes boxes q k).hi : ℝ) := by
  induction k with
  | zero => exact h 0 (Nat.le_refl 0)
  | succ k ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hn := h (k+1) (Nat.le_refl _)
    change ((max _ _ : Rat):ℝ) ≤ r ∧ r ≤ ((min _ _ : Rat):ℝ)
    rw [Rat.cast_max,Rat.cast_min]
    exact ⟨max_le hp.1 hn.1,le_min hp.2 hn.2⟩

/-- The complete native quadrature represents Mathlib's integral. Neither
native FTC nor the native direct endpoint identity is a prerequisite. -/
theorem cosine_integral_represents (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a ≤ b) :
    Represents (integral B a b ha hb hab)
      (∫ x in (a:ℝ)..(b:ℝ), normalizedCosine x) := by
  intro n
  exact intersect_contains_real n n (fun k _ => fixedMesh_contains_integral B ha hb hab k n)

end MathlibComparison
