import EulerCotangent
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
noncomputable section
open scoped Topology NNReal ENNReal
open Filter Finset PowerSeries
namespace EulerEven

def scale : ℂ := 2*Real.pi*Complex.I
def exponentialSeries : PowerSeries ℂ := rescale scale (PowerSeries.exp ℂ)
def cotangentSeries : PowerSeries ℂ := 1-X^2*zetaSeries

def cotangentFunction (z : ℂ) : ℂ := 1-z^2*zetaFunction z

lemma scale_ne_zero : scale ≠ 0 := by
  simp [scale, Real.pi_ne_zero, Complex.I_ne_zero]

lemma represents_one : Represents (1 : PowerSeries ℂ) (fun _ => 1) := by
  simpa using represents_C 1

lemma represents_cotangent : Represents cotangentSeries cotangentFunction := by
  change Represents (1-X^2*zetaSeries) (fun z => 1-z^2*zetaFunction z)
  simpa only [pow_two] using
    represents_one.sub ((represents_X.mul represents_X).mul represents_zetaSeries)

lemma exponential_ne_one {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    Complex.exp (scale*z) ≠ 1 := by
  intro h
  obtain ⟨m,hm⟩ := Complex.exp_eq_one_iff.mp h
  apply integerComplement_of_small hz hz0
  refine ⟨m, ?_⟩
  apply mul_left_cancel₀ scale_ne_zero
  calc
    scale*(m:ℂ) = (m:ℂ)*(2*Real.pi*Complex.I) := by dsimp [scale]; ring
    _ = scale*z := hm.symm

lemma cotangent_exponential_identity {z : ℂ} (hz : ‖z‖ < 1) :
    cotangentFunction z * (Complex.exp (scale*z)-1) =
      (scale/2)*z*(Complex.exp (scale*z)+1) := by
  by_cases hz0 : z=0
  · simp [cotangentFunction,hz0]
  rw [cotangentFunction, ← cotangent_generating hz hz0, Complex.cot_pi_eq_exp_ratio]
  have he := exponential_ne_one hz hz0
  have hden : 1-Complex.exp (scale*z) ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
  change (Real.pi:ℂ)*z*((Complex.exp (scale*z)+1)/(Complex.I*(1-Complex.exp (scale*z))))*
    (Complex.exp (scale*z)-1) = (scale/2)*z*(Complex.exp (scale*z)+1)
  generalize heq : Complex.exp (scale*z) = e at *
  dsimp [scale]
  field_simp
  simp [Complex.I_sq]
  ring

/-- The analytic product identity transported to formal coefficients. -/
lemma cotangent_series_identity :
    cotangentSeries*(exponentialSeries-1) =
      C (scale/2)*X*(exponentialSeries+1) := by
  have hl := represents_cotangent.mul ((represents_exp scale).sub represents_one)
  have hr := ((represents_C (scale/2)).mul represents_X).mul ((represents_exp scale).add represents_one)
  apply Represents.unique (f := fun z => (scale/2)*z*(Complex.exp (scale*z)+1))
  · exact hl.congr (fun z hz => cotangent_exponential_identity hz)
  · exact hr

lemma exponentialSeries_sub_one_ne_zero : exponentialSeries-1 ≠ 0 := by
  intro h
  have hc := congrArg (coeff 1) h
  simp [exponentialSeries, coeff_rescale, coeff_exp] at hc
  exact scale_ne_zero hc

/-- Uniqueness of the formal Bernoulli generating function. -/
lemma cotangentSeries_eq_bernoulli :
    cotangentSeries = rescale scale (bernoulliPowerSeries ℂ) + C (scale/2)*X := by
  have hb := congrArg (rescale scale) (bernoulliPowerSeries_mul_exp_sub_one ℂ)
  simp only [map_mul, map_sub, map_one, rescale_X] at hb
  have h : (cotangentSeries-C (scale/2)*X)*(exponentialSeries-1) =
      rescale scale (bernoulliPowerSeries ℂ)*(exponentialSeries-1) := by
    rw [show rescale scale (bernoulliPowerSeries ℂ)*(exponentialSeries-1) = C scale * X from hb]
    rw [sub_mul, cotangent_series_identity]
    rw [show C scale = C (scale/2)+C (scale/2) by rw [← map_add]; congr 1; ring]
    ring
  exact sub_eq_iff_eq_add.mp ((mul_right_cancel₀ exponentialSeries_sub_one_ne_zero) h)

lemma even_coefficient (m : ℕ) :
    -2*(zetaTail (2*m):ℂ) =
      scale^(2*m+2)*(bernoulli (2*m+2):ℂ)/(Nat.factorial (2*m+2):ℂ) := by
  have h := congrArg (coeff (2*m+2)) cotangentSeries_eq_bernoulli
  have hn0 : 2*m+2 ≠ 0 := by omega
  have hn1 : 2*m+2 ≠ 1 := by omega
  simpa [cotangentSeries, coeff_X_pow_mul, coeff_rescale, bernoulliPowerSeries,
    zetaSeries, hn0, hn1, pow_mul, mul_div_assoc, show (1:ℂ)+1=2 by norm_num] using h

lemma scale_even_pow (m : ℕ) :
    scale^(2*m+2) = (-1:ℂ)^(m+1)*(2*Real.pi:ℂ)^(2*m+2) := by
  have hi : Complex.I^(2*m+2) = (-1:ℂ)^(m+1) := by
    rw [show 2*m+2=2*(m+1) by omega, pow_mul, Complex.I_sq]
  simp only [scale, mul_pow, hi]
  ring

/-- Euler's evaluation for every positive even exponent. -/
theorem zetaTail_even (m : ℕ) :
    zetaTail (2*m) = (-1:ℝ)^(m+2)*(bernoulli (2*m+2):ℝ)*
      (2*Real.pi)^(2*m+2)/(2*(Nat.factorial (2*m+2):ℝ)) := by
  have h := even_coefficient m
  rw [scale_even_pow] at h
  have hc : (zetaTail (2*m):ℂ) = (-1:ℂ)^(m+2)*(bernoulli (2*m+2):ℂ)*
      (2*Real.pi:ℂ)^(2*m+2)/(2*(Nat.factorial (2*m+2):ℂ)) := by
    rw [show m+2=(m+1)+1 by omega, pow_succ]
    have hf : (Nat.factorial (2*m+2):ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*m+2)
    field_simp at h ⊢
    linear_combination -h
  exact_mod_cast hc

/-- The Dirichlet series, indexed from one, has Euler's Bernoulli value. -/
theorem hasSum_even_zeta (m : ℕ) (hm : 0 < m) :
    HasSum (fun k : ℕ => 1/((k:ℝ)+1)^(2*m))
      ((-1:ℝ)^(m+1)*(bernoulli (2*m):ℝ)*(2*Real.pi)^(2*m)/
        (2*(Nat.factorial (2*m):ℝ))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have h := (zetaTail_summable (2*n)).hasSum
  rw [show (∑' k : ℕ, 1/((k:ℝ)+1)^(2*n+2)) = zetaTail (2*n) from rfl,
    zetaTail_even] at h
  simpa [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_assoc] using h

private lemma bernoulli_five_prime : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

private lemma bernoulli_six_prime : bernoulli' 6 = 1/42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli_five_prime, Nat.choose]

private lemma bernoulli_seven_prime : bernoulli' 7 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

private lemma bernoulli_eight_prime : bernoulli' 8 = -1/30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli_five_prime, bernoulli_six_prime,
    bernoulli_seven_prime, Nat.choose]

/-- Concrete checks of the general theorem, without importing zeta evaluations. -/
theorem hasSum_four : HasSum (fun k : ℕ => 1/((k:ℝ)+1)^4) (Real.pi^4/90) := by
  have h := hasSum_even_zeta 2 (by decide)
  have hb : bernoulli 4 = (-1/30:ℚ) := by norm_num [bernoulli]
  norm_num [hb, mul_pow] at h
  convert! h using 1 <;> ring_nf

theorem hasSum_six : HasSum (fun k : ℕ => 1/((k:ℝ)+1)^6) (Real.pi^6/945) := by
  have h := hasSum_even_zeta 3 (by decide)
  have hb : bernoulli 6 = (1/42:ℚ) := by norm_num [bernoulli, bernoulli_six_prime]
  norm_num [hb, mul_pow] at h
  convert! h using 1 <;> ring_nf

theorem hasSum_eight : HasSum (fun k : ℕ => 1/((k:ℝ)+1)^8) (Real.pi^8/9450) := by
  have h := hasSum_even_zeta 4 (by decide)
  have hb : bernoulli 8 = (-1/30:ℚ) := by norm_num [bernoulli, bernoulli_eight_prime]
  norm_num [hb, mul_pow] at h
  convert! h using 1 <;> ring_nf

end EulerEven
