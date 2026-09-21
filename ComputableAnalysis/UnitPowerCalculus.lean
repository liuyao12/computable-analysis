import ComputableAnalysis.CartwrightMoments
import ComputableAnalysis.FiniteSamplePowers

/-! Reusable finite power estimates and differentiation of powers of sample models.
No completed real number or integral evaluation is used. -/
namespace ComputableAnalysis.UnitPowerCalculus
open ClosedArctanInverse CartwrightMoments FiniteSampleCalculus

theorem abs_le_unit {x : Rat} (hx : Unit x) : qabs x ≤ 1 := by
  rw [qabs_eq_self_of_nonneg hx.1]; exact hx.2

theorem power_difference {x y : Rat} (hx : Unit x) (hy : Unit y) (n : Nat) :
    qabs (x^n-y^n) ≤ (n:Rat)*qabs (x-y) := by
  induction n with
  | zero => simp only [Rat.pow_zero,Rat.sub_self,show ((0:Nat):Rat)=0 by decide +kernel,Rat.zero_mul]; decide +kernel
  | succ n ih =>
    have h1 := mul_abs_bound (by decide : (0:Rat)≤1) (abs_le_unit hx) ih
    have h2 := mul_abs_bound (by decide : (0:Rat)≤1) (abs_le_unit (power_unit hy n))
      (show qabs (x-y)≤qabs (x-y) from Rat.le_refl)
    have ht := qabs_add_le (x*(x^n-y^n)) (y^n*(x-y))
    have he : x*(x^n-y^n)+y^n*(x-y)=x^(n+1)-y^(n+1) := by
      simp only [Rat.pow_succ]; grind only
    rw [he] at ht
    simp only [Rat.natCast_add,Rat.natCast_ofNat]
    grind only


end ComputableAnalysis.UnitPowerCalculus
