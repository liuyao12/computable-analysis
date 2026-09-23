import EulerSeries

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
noncomputable section
open scoped Topology NNReal ENNReal
open Filter Finset PowerSeries
namespace EulerEven

def zetaTail (n : ℕ) : ℝ := ∑' k : ℕ, 1 / ((k:ℝ)+1)^(n+2)

lemma reciprocal_bound (n k : ℕ) :
    1 / ((k:ℝ)+1)^(n+2) ≤ 1 / ((k:ℝ)+1)^2 := by
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_right₀ (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
  omega

lemma zetaTail_summable (n : ℕ) : Summable (fun k : ℕ => 1 / ((k:ℝ)+1)^(n+2)) :=
  EulerBasel.total_summable.of_nonneg_of_le (fun _ => by positivity) (reciprocal_bound n)

lemma zetaTail_bounds (n : ℕ) : 0 ≤ zetaTail n ∧ zetaTail n ≤ 2 := by
  have hbase : EulerBasel.total ≤ 2 :=
    le_of_tendsto EulerBasel.total_summable.hasSum.tendsto_sum_nat
      (Eventually.of_forall fun N => (EulerBasel.sum_bounds N).2)
  exact ⟨tsum_nonneg (fun _ => by positivity),
    ((zetaTail_summable n).tsum_le_tsum (reciprocal_bound n) EulerBasel.total_summable).trans hbase⟩

def zetaSeries : PowerSeries ℂ := mk (fun n => (1+(-1:ℂ)^n)*(zetaTail n : ℂ))
def zetaFunction (z : ℂ) : ℂ := ∑' n, coeff n zetaSeries * z^n

lemma parity_bound (n : ℕ) : ‖(1:ℂ)+(-1:ℂ)^n‖ ≤ 2 := by
  calc
    _ ≤ ‖(1:ℂ)‖ + ‖(-1:ℂ)^n‖ := norm_add_le _ _
    _ = 2 := by norm_num

lemma zetaSeries_bound (n : ℕ) : ‖coeff n zetaSeries‖ ≤ 4 := by
  simp only [zetaSeries, coeff_mk, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (zetaTail_bounds n).1]
  exact (mul_le_mul (parity_bound n) (zetaTail_bounds n).2 (zetaTail_bounds n).1 (by norm_num)).trans_eq (by norm_num)

lemma represents_zetaSeries : Represents zetaSeries zetaFunction := by
  intro z hz
  have hn : Summable (fun n => ‖coeff n zetaSeries * z^n‖) := by
    apply ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left 4).of_nonneg_of_le
      (fun _ => norm_nonneg _)
    intro n
    simpa [norm_mul, norm_pow] using mul_le_mul_of_nonneg_right (zetaSeries_bound n) (pow_nonneg (norm_nonneg z) n)
  exact ⟨hn.of_norm.hasSum,hn⟩

def doubleTerm (z : ℂ) (n k : ℕ) : ℂ :=
  ((1+(-1:ℂ)^n) / ((k:ℂ)+1)^(n+2))*z^n

lemma doubleTerm_bound (z : ℂ) (n k : ℕ) :
    ‖doubleTerm z n k‖ ≤ (2*‖z‖^n)*(1/((k:ℝ)+1)^2) := by
  have ha : ‖(k:ℂ)+1‖ = (k:ℝ)+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using (norm_natCast (α:=ℂ) (k+1))
  simp only [doubleTerm, norm_mul, norm_div, norm_pow, ha]
  calc
    _ ≤ (2 / ((k:ℝ)+1)^(n+2))*‖z‖^n := by
      gcongr
      exact parity_bound n
    _ = (2*‖z‖^n)*(1/((k:ℝ)+1)^(n+2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_bound n k) (by positivity)

lemma doubleTerm_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun p : ℕ × ℕ => doubleTerm z p.1 p.2) := by
  apply (((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left 2).mul_of_nonneg
    EulerBasel.total_summable (fun _ => by positivity) (fun _ => by positivity)).of_norm_bounded
  intro p
  exact doubleTerm_bound z p.1 p.2

lemma doubleTerm_sum (z : ℂ) (n : ℕ) :
    ∑' k, doubleTerm z n k = coeff n zetaSeries * z^n := by
  simp only [doubleTerm, tsum_mul_right, div_eq_mul_inv, tsum_mul_left, zetaSeries, coeff_mk]
  rw [zetaTail, Complex.ofReal_tsum]
  simp

lemma norm_div_nat_succ_lt_one {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    ‖z/((k:ℂ)+1)‖ < 1 := by
  rw [norm_div, show ‖(k:ℂ)+1‖ = (k:ℝ)+1 by simpa only [Nat.cast_add, Nat.cast_one] using (norm_natCast (α:=ℂ) (k+1))]
  apply (div_lt_one (by positivity)).2
  have := Nat.cast_nonneg (α:=ℝ) k
  linarith

lemma doubleTerm_geometric {z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    HasSum (fun n => doubleTerm z n k)
      (1/((k:ℂ)+1)^2 * (1/(1-z/((k:ℂ)+1)) + 1/(1+z/((k:ℂ)+1)))) := by
  have h := ((hasSum_geometric_of_norm_lt_one (norm_div_nat_succ_lt_one hz k)).add
    (hasSum_geometric_of_norm_lt_one (ξ := -z/((k:ℂ)+1)) (by simpa using norm_div_nat_succ_lt_one hz k))).mul_left (1/((k:ℂ)+1)^2)
  have ht : (fun n => doubleTerm z n k) = (fun n =>
      1/((k:ℂ)+1)^2*((z/((k:ℂ)+1))^n+(-z/((k:ℂ)+1))^n)) := by
    funext n
    dsimp [doubleTerm]
    rw [neg_div, neg_pow (z/((k:ℂ)+1))]
    simp only [pow_add, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [ht]
  simpa only [neg_div, sub_neg_eq_add, one_div] using h

lemma zetaFunction_partialFractions {z : ℂ} (hz : ‖z‖ < 1) :
    zetaFunction z = ∑' k : ℕ, 1/((k:ℂ)+1)^2 *
      (1/(1-z/((k:ℂ)+1)) + 1/(1+z/((k:ℂ)+1))) := by
  unfold zetaFunction
  simp_rw [← doubleTerm_sum]
  rw [show (∑' n, ∑' k, doubleTerm z n k) = (∑' k, ∑' n, doubleTerm z n k) from
    (doubleTerm_summable hz).tsum_comm.symm]
  exact tsum_congr (fun k => (doubleTerm_geometric hz k).tsum_eq)

lemma integerComplement_of_small {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    z ∈ Complex.integerComplement := by
  intro ⟨m, hm⟩
  have hm0 : m ≠ 0 := by intro h; subst m; simp at hm; exact hz0 hm.symm
  have h1 : (1:ℝ) ≤ |(m:ℝ)| := by exact_mod_cast Int.one_le_abs hm0
  have hn : ‖(m:ℂ)‖ = |(m:ℝ)| := by simp
  rw [← hm, hn] at hz
  linarith

lemma cotangent_generating {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    (Real.pi:ℂ)*z*Complex.cot (Real.pi*z) = 1-z^2*zetaFunction z := by
  have hi := integerComplement_of_small hz hz0
  rw [zetaFunction_partialFractions hz]
  have hc := cot_series_rep' hi
  have ht (k : ℕ) : z*(1/(z-((k:ℂ)+1))+1/(z+((k:ℂ)+1))) =
      -z^2*(1/((k:ℂ)+1)^2*(1/(1-z/((k:ℂ)+1))+1/(1+z/((k:ℂ)+1)))) := by
    have ha : (k:ℂ)+1 ≠ 0 := by exact_mod_cast (show (k:ℝ)+1 ≠ 0 by positivity)
    have hm : z-((k:ℂ)+1) ≠ 0 := by
      simpa [sub_eq_add_neg] using Complex.integerComplement_add_ne_zero hi (-(k+1):ℤ)
    have hp : z+((k:ℂ)+1) ≠ 0 := by
      simpa using Complex.integerComplement_add_ne_zero hi (k+1:ℤ)
    have hdm : 1-z/((k:ℂ)+1) ≠ 0 := by
      intro h
      apply hm
      field_simp at h
      linear_combination -h
    have hdp : 1+z/((k:ℂ)+1) ≠ 0 := by
      intro h
      apply hp
      field_simp at h
      linear_combination h
    generalize haeq : (k:ℂ)+1 = a at *
    have hma : a-z ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hm))
    have hpa : a+z ≠ 0 := by simpa [add_comm] using hp
    field_simp
    ring
  calc
    _ = 1+z*((Real.pi:ℂ)*Complex.cot (Real.pi*z)-1/z) := by field_simp; ring
    _ = 1+∑' k : ℕ, z*(1/(z-((k:ℂ)+1))+1/(z+((k:ℂ)+1))) := by rw [hc, tsum_mul_left]
    _ = 1+∑' k : ℕ, -z^2*(1/((k:ℂ)+1)^2*(1/(1-z/((k:ℂ)+1))+1/(1+z/((k:ℂ)+1)))) := by simp_rw [ht]
    _ = _ := by rw [tsum_mul_left]; ring

end EulerEven
