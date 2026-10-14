import ComputableAnalysis.ModularForms.TauPositiveProductWeight
import ComputableAnalysis.ModularForms.TauEulerPrefixBounds

/-! Uniform rational bounds for the positive coefficient Euler products. -/
namespace ComputableAnalysis.ModularForms

private theorem factor_bound (s : Rat) (hs : 0≤s) (hsM : s≤(1:Rat)/128)
    (n : Nat) (hn : n≤24) : (1+s)^n≤1+2*(n:Rat)*s := by
  induction n with
  | zero => simp only [Rat.pow_zero,show ((0:Nat):Rat)=0 by rfl,Rat.mul_zero,Rat.zero_mul,Rat.add_zero]; exact Rat.le_refl
  | succ n ih =>
    have hn24 : n≤24 := by omega
    have h := Rat.mul_le_mul_of_nonneg_right (ih hn24) (Rat.add_nonneg (show (0:Rat)≤1 by decide +kernel) hs)
    have hc : (n:Rat)≤24 := Rat.natCast_le_natCast.mpr hn24
    have hns := Rat.mul_le_mul_of_nonneg_right hc hs
    have hs48 := Rat.mul_le_mul_of_nonneg_left hsM (show (0:Rat)≤48 by decide +kernel)
    have hcoef : 2*(n:Rat)*s≤1 := by grind only
    have hm := Rat.mul_le_mul_of_nonneg_right hcoef hs
    rw [Rat.pow_succ,Rat.natCast_add,show ((1:Nat):Rat)=1 by rfl]
    grind only

/-- The positive product is controlled by a small geometric budget. -/
theorem positiveDiscriminantProduct_geometric_bound (r : Rat) (hr : 0≤r)
    (hrM : r≤(1:Rat)/256) (N : Nat) :
    positiveDiscriminantProduct r N≤1+96*tauEulerGeometricBudget r N := by
  have hrhalf : r≤(1:Rat)/2 := Rat.le_trans hrM (by decide +kernel)
  induction N with
  | zero => change (1:Rat)≤1+96*0; grind only
  | succ N ih =>
    have hg := tauEulerGeometricBudget_bound r hr hrhalf N
    have hg96 := Rat.mul_le_mul_of_nonneg_left hg (show (0:Rat)≤96 by decide +kernel)
    have hr192 := Rat.mul_le_mul_of_nonneg_left hrM (show (0:Rat)≤192 by decide +kernel)
    have hP : positiveDiscriminantProduct r N≤2 := by grind only
    have hp : 0≤r^(N+1) := Rat.pow_nonneg hr
    have hfirst := tauEulerGeometricPower_le_first r hr (Rat.le_trans hrM (by decide +kernel)) N
    have hf := factor_bound (r^(N+1)) hp
      (Rat.le_trans hfirst (Rat.le_trans hrM (by decide +kernel))) 24 (Nat.le_refl 24)
    have hm := Rat.mul_le_mul_of_nonneg_left hf (positiveDiscriminantProduct_nonnegative r hr N)
    have hinc := Rat.mul_le_mul_of_nonneg_right hP hp
    change positiveDiscriminantProduct r N*(1+r^(N+1))^24≤_
    change _≤1+96*(tauEulerGeometricBudget r N+r^(N+1))
    have hc : (2:Rat)*((24:Nat):Rat)=48 := by decide +kernel
    rw [hc] at hm
    grind only

/-- A single rational bound controls every product length. -/
theorem positiveDiscriminantProduct_uniform_bound (r : Rat) (hr : 0≤r)
    (hrM : r≤(1:Rat)/256) (N : Nat) : positiveDiscriminantProduct r N≤2 := by
  have h := positiveDiscriminantProduct_geometric_bound r hr hrM N
  have hg := tauEulerGeometricBudget_bound r hr (Rat.le_trans hrM (by decide +kernel)) N
  have hm := Rat.mul_le_mul_of_nonneg_left hg (show (0:Rat)≤96 by decide +kernel)
  have hr192 := Rat.mul_le_mul_of_nonneg_left hrM (show (0:Rat)≤192 by decide +kernel)
  grind only

/-- Weighted absolute majorants are bounded uniformly in both cutoffs. -/
theorem discriminantAbsoluteMajorant_uniform_weight_bound (r : Rat) (hr : 0≤r)
    (hrM : r≤(1:Rat)/256) (N L : Nat) :
    positiveCoefficientWeight (discriminantAbsoluteMajorant N) r L≤2 :=
  Rat.le_trans (discriminantAbsoluteMajorant_weight_bound r hr N L)
    (positiveDiscriminantProduct_uniform_bound r hr hrM N)

end ComputableAnalysis.ModularForms
