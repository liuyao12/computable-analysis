import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Euler's coefficient argument, with a uniform finite-product remainder.
No Basel evaluation, Bernoulli Fourier series, or zeta-value theorem is used. -/
noncomputable section
namespace EulerBasel
open Filter Finset
open scoped Topology

/-- A quantitative replacement for formally discarding higher product terms. -/
theorem product_remainder (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k ∧ a k ≤ 1) (N : ℕ) :
    0 ≤ (∏ k ∈ range N, (1-a k)) - (1-∑ k ∈ range N, a k) ∧
    (∏ k ∈ range N, (1-a k)) - (1-∑ k ∈ range N, a k) ≤
      (∑ k ∈ range N, a k)^2/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : 0 ≤ ∑ k ∈ range N, a k := sum_nonneg (fun k _ => (ha k).1)
    have hR := mul_nonneg (sub_nonneg.mpr (ha N).2) ih.1
    have hS := mul_nonneg (ha N).1 hs
    have hA := mul_nonneg (ha N).1 ih.1
    rw [prod_range_succ, sum_range_succ]
    constructor <;> nlinarith [sq_nonneg (a N)]

def sum (N : ℕ) : ℝ := ∑ k ∈ range N, 1/((k:ℝ)+1)^2
def product (x : ℝ) (N : ℕ) : ℝ := ∏ k ∈ range N, (1-x^2/((k:ℝ)+1)^2)
def total : ℝ := ∑' k : ℕ, 1/((k:ℝ)+1)^2

theorem sum_bounds (N : ℕ) : 0 ≤ sum N ∧ sum N ≤ 2 := by
  have strong : sum N ≤ 2-2/((N:ℝ)+1) := by
    induction N with
    | zero => norm_num [sum]
    | succ N ih =>
      have h1 : (0:ℝ)<N+1 := by positivity
      have h2 : (0:ℝ)<N+2 := by positivity
      have step : 1/((N:ℝ)+1)^2 ≤ 2/((N:ℝ)+1)-2/((N:ℝ)+2) := by
        field_simp
        nlinarith [show (0:ℝ)≤N by positivity]
      simp only [sum, sum_range_succ, Nat.cast_add, Nat.cast_one, show (N:ℝ)+1+1=N+2 by ring] at *
      linarith
  exact ⟨sum_nonneg (fun _ _ => by positivity),by have := div_nonneg (by norm_num : (0:ℝ)≤2) (by positivity : (0:ℝ)≤N+1);linarith⟩

theorem product_quadratic_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    0 ≤ product x N-(1-x^2*sum N) ∧
    product x N-(1-x^2*sum N) ≤ 2*x^4 := by
  have h := product_remainder (fun k => x^2/((k:ℝ)+1)^2) (by
    intro k
    have hk : (1:ℝ)≤((k:ℝ)+1)^2 := by
      have : (0:ℝ)≤k := by positivity
      nlinarith
    constructor
    · positivity
    · apply (div_le_one (by positivity)).2
      nlinarith) N
  have hs : (∑ k ∈ range N, x^2/((k:ℝ)+1)^2)=x^2*sum N := by
    simp [sum, mul_sum, div_eq_mul_inv]
  rw [hs] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hb := sum_bounds N
  have hh : (sum N)^2≤4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg (x^2))
  nlinarith

theorem total_summable : Summable (fun k : ℕ => 1/((k:ℝ)+1)^2) := by
  simpa [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))

theorem sine_product_limit {x : ℝ} (hx : x ≠ 0) :
    Tendsto (product x) atTop (𝓝 (Real.sin (Real.pi*x)/(Real.pi*x))) := by
  have h := (Real.tendsto_euler_sin_prod x).div_const (Real.pi*x)
  have hn : Real.pi*x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  change Tendsto (fun N => ∏ k ∈ range N, (1-x^2/((k:ℝ)+1)^2)) _ _
  simpa only [mul_div_cancel_left₀ _ hn] using h

theorem infinite_product_bound {x : ℝ} (hx : 0<x) (hx1 : x≤1) :
    0 ≤ Real.sin (Real.pi*x)/(Real.pi*x)-(1-x^2*total) ∧
    Real.sin (Real.pi*x)/(Real.pi*x)-(1-x^2*total) ≤ 2*x^4 := by
  have hp := sine_product_limit (ne_of_gt hx)
  have hs : Tendsto sum atTop (𝓝 total) := total_summable.hasSum.tendsto_sum_nat
  have ht := hp.sub ((tendsto_const_nhds (x:=(1:ℝ))).sub (hs.const_mul (x^2)))
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun N => (product_quadratic_bound hx.le hx1 N).1),
    le_of_tendsto ht (Eventually.of_forall fun N => (product_quadratic_bound hx.le hx1 N).2)⟩

/-- Explicit coefficient error after taking the product limit. -/
theorem coefficient_error {x : ℝ} (hx : 0<x) (hx1 : x≤1) (hpx : Real.pi*x≤1) :
    |total-Real.pi^2/6| ≤ (2+Real.pi^4/100)*x^2 := by
  have hprod := infinite_product_bound hx hx1
  have hp : 0<Real.pi*x := mul_pos Real.pi_pos hx
  have hsin := Real.sin_bound (x:=Real.pi*x) (by rwa [abs_of_pos hp])
  rw [abs_of_pos hp, abs_le] at hsin
  have hid : Real.sin (Real.pi*x) = (Real.pi*x)*(Real.sin (Real.pi*x)/(Real.pi*x)) := by field_simp
  have hlo := mul_le_mul_of_nonneg_left hprod.1 hp.le
  have hhi := mul_le_mul_of_nonneg_left hprod.2 hp.le
  have hpower : 0<(Real.pi*x)*x^2 := mul_pos hp (sq_pos_of_pos hx)
  have hlo' : ((Real.pi*x)*x^2)*(-((2+Real.pi^4/100)*x^2)) ≤
      ((Real.pi*x)*x^2)*(total-Real.pi^2/6) := by nlinarith
  have hhi' : ((Real.pi*x)*x^2)*(total-Real.pi^2/6) ≤
      ((Real.pi*x)*x^2)*((2+Real.pi^4/100)*x^2) := by nlinarith
  exact abs_le.mpr ⟨(mul_le_mul_iff_right₀ hpower).mp hlo', (mul_le_mul_iff_right₀ hpower).mp hhi'⟩

/-- Euler's Basel evaluation, obtained from the sine product and a justified
coefficient comparison. -/
theorem total_eq : total=Real.pi^2/6 := by
  let x : ℕ → ℝ := fun n => (1/(Real.pi+1))*(1/((n:ℝ)+1))
  have hxlim : Tendsto x atTop (𝓝 0) := by
    simpa [x] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (1/(Real.pi+1))
  have hbound : ∀ n, |total-Real.pi^2/6|≤(2+Real.pi^4/100)*(x n)^2 := by
    intro n
    have hn : (1:ℝ)≤(n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
    have hnpos : (0:ℝ)<(n:ℝ)+1 := by positivity
    have hp : 0<Real.pi+1 := by positivity
    have hden : (1:ℝ)≤(Real.pi+1)*((n:ℝ)+1) := by nlinarith [Real.pi_pos]
    have hdenpi : Real.pi≤(Real.pi+1)*((n:ℝ)+1) := by nlinarith [Real.pi_pos]
    have hxform : x n = 1/((Real.pi+1)*((n:ℝ)+1)) := by simp [x, one_div, mul_inv_rev, mul_comm]
    apply coefficient_error
    · dsimp [x];positivity
    · rw [hxform];exact (div_le_one (by positivity)).2 hden
    · rw [hxform, mul_one_div];exact (div_le_one (by positivity)).2 hdenpi
  have hlim : Tendsto (fun n => (2+Real.pi^4/100)*(x n)^2) atTop (𝓝 0) := by
    simpa using (hxlim.pow 2).const_mul (2+Real.pi^4/100)
  have hzero := ge_of_tendsto hlim (Eventually.of_forall hbound)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

theorem hasSum_reciprocal_squares :
    HasSum (fun k : ℕ => 1/((k:ℝ)+1)^2) (Real.pi^2/6) := by
  rw [← total_eq]
  exact total_summable.hasSum
end EulerBasel
