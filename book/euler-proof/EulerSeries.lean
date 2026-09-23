import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import EulerBasel

noncomputable section
open scoped Topology NNReal ENNReal
open Filter Finset PowerSeries
namespace EulerEven

/-- Absolute power-series representation on the unit disk. -/
def Represents (p : PowerSeries ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, ‖z‖ < 1 → HasSum (fun n => coeff n p * z^n) (f z) ∧
    Summable (fun n => ‖coeff n p * z^n‖)

lemma Represents.at_zero {p : PowerSeries ℂ} {f : ℂ → ℂ} (h : Represents p f) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (fun n => coeff n p)) 0 := by
  refine ⟨(1/2 : ℝ≥0), ?_⟩
  constructor
  · apply FormalMultilinearSeries.le_radius_of_summable
    simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using
      (h (1/2) (by norm_num)).2
  · norm_num
  · intro z hz
    have hz' : ‖z‖ < (1/2 : ℝ) := by
      change edist z 0 < ((1/2 : ℝ≥0) : ℝ≥0∞) at hz
      simpa only [edist_dist, dist_zero_right] using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1/2)).mp (by simpa using hz)
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      (h z (by linarith)).1

lemma Represents.unique {p q : PowerSeries ℂ} {f : ℂ → ℂ}
    (hp : Represents p f) (hq : Represents q f) : p = q := by
  have h := hp.at_zero.eq_formalMultilinearSeries hq.at_zero
  ext n
  simpa using congrArg (fun s => s.coeff n) h

lemma Represents.congr {p : PowerSeries ℂ} {f g : ℂ → ℂ} (h : Represents p f)
    (he : ∀ z, ‖z‖ < 1 → f z = g z) : Represents p g := by
  intro z hz
  simpa only [he z hz] using h z hz

lemma Represents.add {p q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hp : Represents p f) (hq : Represents q g) : Represents (p+q) (fun z => f z+g z) := by
  intro z hz
  have a := hp z hz
  have b := hq z hz
  constructor
  · simpa [map_add, add_mul] using a.1.add b.1
  · simpa [map_add, add_mul] using ((a.2.add b.2).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_add_le _ _))

lemma Represents.neg {p : PowerSeries ℂ} {f : ℂ → ℂ}
    (hp : Represents p f) : Represents (-p) (fun z => -f z) := by
  intro z hz
  constructor
  · simpa using (hp z hz).1.neg
  · simpa using (hp z hz).2

lemma Represents.sub {p q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hp : Represents p f) (hq : Represents q g) : Represents (p-q) (fun z => f z-g z) := by
  simpa [sub_eq_add_neg] using hp.add hq.neg

lemma Represents.mul {p q : PowerSeries ℂ} {f g : ℂ → ℂ}
    (hp : Represents p f) (hq : Represents q g) : Represents (p*q) (fun z => f z*g z) := by
  intro z hz
  have a := hp z hz
  have b := hq z hz
  have ht (n : ℕ) : (∑ kl ∈ Finset.antidiagonal n,
      (coeff kl.1 p * z^kl.1)*(coeff kl.2 q * z^kl.2)) = coeff n (p*q)*z^n := by
    rw [coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro kl hkl
    have he := Finset.mem_antidiagonal.mp hkl
    rw [← he, pow_add]
    ring
  have hn := summable_norm_sum_mul_antidiagonal_of_summable_norm a.2 b.2
  simp_rw [ht] at hn
  refine ⟨?_, hn⟩
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm a.2 b.2
  rw [a.1.tsum_eq, b.1.tsum_eq] at he
  simp_rw [ht] at he
  change HasSum _ (f z * g z)
  rw [he]
  exact hn.of_norm.hasSum

lemma represents_C (c : ℂ) : Represents (C c) (fun _ => c) := by
  intro z hz
  constructor
  · simpa using (hasSum_single 0 (f := fun n => coeff n (C c) * z^n)
      (fun n hn => by simp [coeff_C, hn]))
  · exact (hasSum_single 0 (f := fun n => ‖coeff n (C c) * z^n‖)
      (fun n hn => by simp [coeff_C, hn])).summable

lemma represents_X : Represents (X : PowerSeries ℂ) (fun z => z) := by
  intro z hz
  constructor
  · simpa using (hasSum_single 1 (f := fun n => coeff n (X : PowerSeries ℂ) * z^n)
      (fun n hn => by simp [coeff_X, hn]))
  · exact (hasSum_single 1 (f := fun n => ‖coeff n (X : PowerSeries ℂ) * z^n‖)
      (fun n hn => by simp [coeff_X, hn])).summable

lemma represents_exp (c : ℂ) : Represents (rescale c (PowerSeries.exp ℂ)) (fun z => Complex.exp (c*z)) := by
  intro z hz
  constructor
  · simpa [Complex.exp_eq_exp_ℂ, coeff_rescale, coeff_exp, mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using NormedSpace.expSeries_div_hasSum_exp (c*z)
  · simpa [coeff_rescale, coeff_exp, norm_mul, norm_pow, mul_pow, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using (Real.summable_pow_div_factorial (‖c‖*‖z‖))

end EulerEven
