import ComputableAnalysis.ModularForms.TauWeightedMajorant

/-! Weighted coefficient domination by executable positive Euler products. -/
namespace ComputableAnalysis.ModularForms

/-- Literal rational positive Euler product. -/
def positiveDiscriminantProduct (r : Rat) : Nat → Rat
  | 0 => 1
  | N+1 => positiveDiscriminantProduct r N*(1+r^(N+1))^24

theorem positiveDiscriminantProduct_nonnegative (r : Rat) (hr : 0≤r) (N : Nat) :
    0≤positiveDiscriminantProduct r N := by
  induction N with
  | zero => change (0:Rat)≤1; decide +kernel
  | succ N ih => exact Rat.mul_nonneg ih (Rat.pow_nonneg (Rat.add_nonneg (by decide +kernel) (Rat.pow_nonneg hr)))

/-- Iterating the factor estimate controls every coefficient cutoff. -/
theorem positiveCoefficientWeight_factorPower_bound (a : Nat → Nat) (r : Rat) (hr : 0≤r)
    (m k L : Nat) :
    positiveCoefficientWeight (positiveFactorPower m k a) r L≤
      (1+r^m)^k*positiveCoefficientWeight a r L := by
  have hb : 0≤1+r^m := Rat.add_nonneg (by decide +kernel) (Rat.pow_nonneg hr)
  induction k with
  | zero => simp only [positiveFactorPower,Rat.pow_zero,Rat.one_mul]; exact Rat.le_refl
  | succ k ih =>
    have hs := positiveCoefficientWeight_addShift_bound (positiveFactorPower m k a) r hr m L
    have hm := Rat.mul_le_mul_of_nonneg_left ih hb
    change positiveCoefficientWeight (addShift m (positiveFactorPower m k a)) r L≤_
    rw [Rat.pow_succ]
    grind only

private theorem unit_weight_bound (r : Rat) (L : Nat) :
    positiveCoefficientWeight (fun n => if n=0 then 1 else 0) r L≤1 := by
  cases L with
  | zero => change (0:Rat)≤1; decide +kernel
  | succ L =>
    have he : ∀ n, positiveCoefficientWeight (fun n => if n=0 then 1 else 0) r (n+1)=1 := by
      intro n
      induction n with
      | zero => change (0:Rat)+(1:Rat)*r^0=1; simp only [Rat.pow_zero]; grind only
      | succ n ih =>
        rw [positiveCoefficientWeight,ih]
        simp only [if_neg (show n+1≠0 by omega),show ((0:Nat):Rat)=0 by rfl,Rat.zero_mul,Rat.add_zero]
    rw [he]
    exact Rat.le_refl

/-- The actual positive coefficient majorants have uniform-in-cutoff weighted bounds. -/
theorem discriminantAbsoluteMajorant_weight_bound (r : Rat) (hr : 0≤r) (N L : Nat) :
    positiveCoefficientWeight (discriminantAbsoluteMajorant N) r L≤positiveDiscriminantProduct r N := by
  induction N with
  | zero => exact unit_weight_bound r L
  | succ N ih =>
    have hf := positiveCoefficientWeight_factorPower_bound (discriminantAbsoluteMajorant N) r hr (N+1) 24 L
    have hm := Rat.mul_le_mul_of_nonneg_left ih
      (Rat.pow_nonneg (Rat.add_nonneg (show (0:Rat)≤1 by decide +kernel) (Rat.pow_nonneg hr)) : 0≤(1+r^(N+1))^24)
    change positiveCoefficientWeight (positiveFactorPower (N+1) 24 (discriminantAbsoluteMajorant N)) r L≤_
    change _≤positiveDiscriminantProduct r N*(1+r^(N+1))^24
    grind only

end ComputableAnalysis.ModularForms
