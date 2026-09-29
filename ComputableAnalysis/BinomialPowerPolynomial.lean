import ComputableAnalysis.ZetaReal.Binomial

/-! Finite binomial identities, independent of improper integrals and Dirichlet sums. -/
namespace ComputableAnalysis.ZetaReal
open FormalPowerSeries

/-- Finite generalized-binomial power polynomial. -/
def powerPolynomial (s : Rat) (K : Nat) (z : Rat) : Rat :=
  sumBelow (fun k => coefficient s k*z^k) K

/-- Coefficient form of `(1-z) f' = (2-s) f`, with `f(0)=1`. -/
theorem binomial_equation (s : Rat) (k : Nat) :
    ((k : Rat)+1)*coefficient s (k+1)-(k : Rat)*coefficient s k =
      (2-s)*coefficient s k := by
  have h := coefficient_step s k
  grind only

/-- The power coefficients are forced by the differential equation and initial value. -/
theorem binomial_unique (s : Rat) (a : Nat → Rat) (ha : a 0=1)
    (hode : ∀ k : Nat, ((k : Rat)+1)*a (k+1)-(k : Rat)*a k=(2-s)*a k) :
    a=coefficient s := by
  funext k
  induction k with
  | zero => exact ha
  | succ k ih =>
    have h := hode k
    have hc := coefficient_step s k
    have hk : 0 < (k : Rat)+1 := by have := Rat.natCast_nonneg (a := k); grind
    apply Rat.le_antisymm
    all_goals
      apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ hk
      rw [ih] at h
      grind only

theorem coefficient_parameter_succ (s : Rat) (k : Nat) :
    coefficient (s+1) (k+1)=coefficient s (k+1)-coefficient s k := by
  induction k with
  | zero => simp only [coefficient]; grind [Rat.div_def]
  | succ k ih =>
    have h1 := coefficient_step (s+1) (k+1)
    have h2 := coefficient_step s (k+1)
    have h3 := coefficient_step s k
    have hk : 0 < (k : Rat)+2 := by have := Rat.natCast_nonneg (a := k); grind
    rw [ih] at h1
    simp only [Rat.natCast_add] at h1 h2
    apply Rat.le_antisymm
    all_goals
      apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+2) ?_ hk
      grind only

theorem powerPolynomial_parameter_succ (s z : Rat) (K : Nat) :
    powerPolynomial (s+1) (K+1) z = (1-z)*powerPolynomial s K z+coefficient s K*z^K := by
  induction K with
  | zero => simp [powerPolynomial, sumBelow_succ, coefficient]
  | succ K ih =>
    have h := coefficient_parameter_succ s K
    change sumBelow _ ((K+1)+1) = _
    rw [sumBelow_succ]
    change powerPolynomial (s+1) (K+1) z+_ = _
    rw [ih, h]
    unfold powerPolynomial
    rw [sumBelow_succ, Rat.pow_succ]
    grind only

theorem coefficient_integer_vanish (p k : Nat) (hk : p < k) :
    coefficient ((p : Rat)+2) k=0 := by
  have hbase : coefficient ((p : Rat)+2) (p+1)=0 := by
    rw [coefficient]; grind [Rat.div_def]
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show p+1 ≤ k by omega)
  rw [hj]
  clear hj hk
  induction j with
  | zero => simpa only [Nat.add_zero] using hbase
  | succ j ih =>
    rw [show p+1+(j+1)=(p+1+j)+1 by omega, coefficient, ih]
    grind [Rat.div_def]

theorem powerPolynomial_integer (p K : Nat) (hK : p < K) (z : Rat) :
    powerPolynomial ((p : Rat)+2) K z=(1-z)^p := by
  induction p generalizing K with
  | zero =>
    cases K with
    | zero => omega
    | succ K =>
      clear hK
      induction K with
      | zero => simp [powerPolynomial, sumBelow_succ, coefficient]; grind
      | succ K ih =>
        have hv := coefficient_integer_vanish 0 (K+1) (by omega)
        unfold powerPolynomial at *
        rw [sumBelow_succ, hv, ih]
        grind
  | succ p ih =>
    cases K with
    | zero => omega
    | succ K =>
      have he : ((p+1 : Nat) : Rat)+2=((p : Rat)+2)+1 := by simp only [Rat.natCast_add]; grind
      rw [he, powerPolynomial_parameter_succ, ih K (by omega), coefficient_integer_vanish p K (by omega), Rat.pow_succ]
      grind only


/-- Uniform coefficient bound on any bounded exponent range. No restriction
relative to the improper-integral threshold is needed on a compact chart. -/
theorem coefficient_growth {s C : Rat} (hC : 1 ≤ C)
    (hs : qabs (2-s) ≤ C-1) (k : Nat) :
    qabs (coefficient s k) ≤ C^k := by
  induction k with
  | zero => simp only [coefficient, Rat.pow_zero]; decide +kernel
  | succ k ih =>
    have hk := Rat.natCast_nonneg (a := k)
    have ha := qabs_add_le (k : Rat) (2-s)
    rw [qabs_eq_self_of_nonneg hk] at ha
    have hprod := Rat.mul_nonneg (show 0 ≤ C-1 by grind) hk
    have hb : qabs ((k : Rat)+2-s) ≤ C*((k : Rat)+1) := by
      rw [show (k : Rat)+2-s=(k : Rat)+(2-s) by grind only]
      grind only
    have he := congrArg qabs (coefficient_step s k)
    rw [qabs_mul, qabs_mul, qabs_eq_self_of_nonneg (by grind : 0 ≤ (k : Rat)+1)] at he
    have h1 := Rat.mul_le_mul_of_nonneg_right hb (qabs_nonneg (coefficient s k))
    have h2 := Rat.mul_le_mul_of_nonneg_left ih
      (Rat.mul_nonneg (show 0 ≤ C by grind) (show 0 ≤ (k : Rat)+1 by grind))
    rw [Rat.pow_succ]
    apply Rat.le_of_mul_le_mul_left (c := (k : Rat)+1) ?_ (by grind)
    grind only

/-- Exact coefficient identity for integration, including the threshold
parameter without dividing by it. -/
theorem coefficient_integral_shift (s : Rat) (k : Nat) :
    ((k : Rat)+1)*coefficient (s+1) (k+1) = (1-s)*coefficient s k := by
  rw [coefficient_parameter_succ]
  have h := coefficient_step s k
  grind only

/-- Finite integrated polynomial, normalized to zero at the origin. -/
def integratedPowerPolynomial (s : Rat) (K : Nat) (z : Rat) : Rat :=
  sumBelow (fun k => coefficient s k*z^(k+1)/((k : Rat)+1)) K

/-- The closed-form identity already holds for finite polynomials. Its proof
uses only coefficient recurrence, so it cannot depend on any infinite tail. -/
theorem integratedPowerPolynomial_identity (s z : Rat) (K : Nat) :
    (s-1)*integratedPowerPolynomial s K z = 1-powerPolynomial (s+1) (K+1) z := by
  induction K with
  | zero => simp [integratedPowerPolynomial, powerPolynomial, sumBelow_succ, coefficient]; grind
  | succ K ih =>
    have h := coefficient_integral_shift s K
    have hk : ((K : Rat)+1) ≠ 0 := by have := Rat.natCast_nonneg (a := K); grind
    have hi := Rat.mul_inv_cancel ((K : Rat)+1) hk
    unfold integratedPowerPolynomial powerPolynomial at *
    rw [sumBelow_succ, sumBelow_succ]
    rw [Rat.div_def]
    have he : (s-1)*(coefficient s K*z^(K+1)*((K : Rat)+1)⁻¹) =
        -coefficient (s+1) (K+1)*z^(K+1) := by
      calc
        _ = -(((K : Rat)+1)*coefficient (s+1) (K+1))*z^(K+1)*((K : Rat)+1)⁻¹ := by rw [h]; grind only
        _ = _ := by grind only
    grind only

end ComputableAnalysis.ZetaReal
