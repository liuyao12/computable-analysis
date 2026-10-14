import ComputableAnalysis.ModularForms.TauPositiveProductUniform

/-! Explicit geometric coefficient majorants on the nome disk. -/
namespace ComputableAnalysis.ModularForms

/-- Each nonnegative summand is bounded by the total weighted prefix. -/
theorem positiveCoefficientWeight_term_bound (a : Nat → Nat) (r : Rat) (hr : 0≤r) (n : Nat) :
    (a n:Rat)*r^n≤positiveCoefficientWeight a r (n+1) := by
  have h := positiveCoefficientWeight_nonnegative a r hr n
  change (a n:Rat)*r^n≤positiveCoefficientWeight a r n+(a n:Rat)*r^n
  grind only

/-- A coefficientwise absolute bound uniform in finite product length. -/
theorem discriminantProduct_weighted_coefficient_bound (N n : Nat) :
    ((discriminantProduct N n).natAbs:Rat)*(1/256:Rat)^n≤2 := by
  have ha := Rat.natCast_le_natCast.mpr (discriminantProduct_absolute_bound N n)
  have hm := Rat.mul_le_mul_of_nonneg_right ha
    (Rat.pow_nonneg (show (0:Rat)≤1/256 by decide +kernel) : 0≤(1/256:Rat)^n)
  exact Rat.le_trans hm (Rat.le_trans
    (positiveCoefficientWeight_term_bound (discriminantAbsoluteMajorant N) (1/256) (by decide +kernel) n)
    (discriminantAbsoluteMajorant_uniform_weight_bound (1/256) (by decide +kernel) Rat.le_refl N (n+1)))

private theorem half_radius_power (n : Nat) :
    (1/512:Rat)^n=(1/256:Rat)^n*(1/2:Rat)^n := by
  induction n with
  | zero => simp only [Rat.pow_zero,Rat.mul_one]
  | succ n ih => rw [Rat.pow_succ,ih,Rat.pow_succ,Rat.pow_succ]; grind only

/-- Geometric term control at the coordinate-power radius of the nome disk. -/
theorem discriminantProduct_geometric_coefficient_bound (N n : Nat) :
    ((discriminantProduct N n).natAbs:Rat)*(1/512:Rat)^n≤2*(1/2:Rat)^n := by
  have h := Rat.mul_le_mul_of_nonneg_right (discriminantProduct_weighted_coefficient_bound N n)
    (Rat.pow_nonneg (show (0:Rat)≤1/2 by decide +kernel) : 0≤(1/2:Rat)^n)
  rw [half_radius_power]
  grind only

/-- The actual tau coefficients inherit the uniform geometric majorant. -/
theorem tau_geometric_coefficient_bound (n : Nat) :
    ((tau (n+1)).natAbs:Rat)*(1/512:Rat)^n≤2*(1/2:Rat)^n :=
  discriminantProduct_geometric_coefficient_bound n n

/-- Executable absolute weighted tail over a finite degree range. -/
def absoluteCoefficientTail (a : Coefficients) (K : Nat) : Nat → Rat
  | 0 => 0
  | M+1 => absoluteCoefficientTail a K M+(a (K+M)).natAbs*(1/512:Rat)^(K+M)

private theorem half_power_add (K M : Nat) :
    (1/2:Rat)^(K+M)=(1/2:Rat)^K*(1/2:Rat)^M := by
  induction M with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ M ih =>
    change (1/2:Rat)^((K+M)+1)=(1/2:Rat)^K*(1/2:Rat)^(M+1)
    rw [Rat.pow_succ,ih,Rat.pow_succ]
    grind only

/-- Absolute finite polynomial tails have a geometric bound independent of product length. -/
theorem discriminantProduct_absolute_tail_bound (N K M : Nat) :
    absoluteCoefficientTail (discriminantProduct N) K M≤4*(1/2:Rat)^K := by
  have haux : ∀ M, absoluteCoefficientTail (discriminantProduct N) K M≤
      4*(1/2:Rat)^K*(1-(1/2:Rat)^M) := by
    intro M
    induction M with
    | zero => simp only [absoluteCoefficientTail,Rat.pow_zero]; grind only
    | succ M ih =>
      have ht := discriminantProduct_geometric_coefficient_bound N (K+M)
      rw [half_power_add] at ht
      rw [absoluteCoefficientTail,Rat.pow_succ]
      grind only
  have hm := Rat.mul_le_mul_of_nonneg_left
    (show 1-(1/2:Rat)^M≤1 by have hp : 0≤(1/2:Rat)^M := Rat.pow_nonneg (by decide +kernel); grind only)
    (Rat.mul_nonneg (show (0:Rat)≤4 by decide +kernel)
      (Rat.pow_nonneg (show (0:Rat)≤1/2 by decide +kernel) : 0≤(1/2:Rat)^K))
  exact Rat.le_trans (haux M) (by simpa only [Rat.mul_one] using hm)

end ComputableAnalysis.ModularForms
