import ComputableAnalysis.PolynomialIntegralWitness
import ComputableAnalysis.LipschitzRectangleBounds

/-! Reflection of finite polynomial integrals, proved by finite secant
estimates and explicit rectangles. No change-of-variable law is assumed. -/
namespace ComputableAnalysis.FormalPowerSeries
open Integral FinitePolynomial

private def reflectedSecant {F f : Rat → Rat} (D : SecantDerivativeBound 2 F f) :
    SecantDerivativeBound 1 (fun x => -F (1-x)) (fun x => f (1-x)) where
  errorCoefficient := D.errorCoefficient
  errorCoefficient_nonneg := D.errorCoefficient_nonneg
  error_bound := by
    intro x h hh hx hxh
    have hb (y : Rat) (hy : qabs y ≤ 1) : qabs (1-y) ≤ 2 := by
      have he := qabs_sub_le 1 y
      rw [qabs_eq_self_of_nonneg (by decide : (0 : Rat) ≤ 1)] at he
      grind only
    have hnh : -h ≠ 0 := by intro he; apply hh; grind only
    have he := D.error_bound (1-x) (-h) hnh (hb x hx)
      (by rw [show 1-x+(-h)=1-(x+h) by grind only]; exact hb (x+h) hxh)
    rw [qabs_neg,show 1-x+(-h)=1-(x+h) by grind only] at he
    have hcan := Rat.mul_inv_cancel h hh
    have hncan := Rat.mul_inv_cancel (-h) hnh
    have hinv : (-h)⁻¹ = -h⁻¹ := by
      calc
        (-h)⁻¹ = (-h)⁻¹*(h*h⁻¹) := by rw [hcan,Rat.mul_one]
        _ = -(((-h)*(-h)⁻¹)*h⁻¹) := by grind only
        _ = -h⁻¹ := by rw [hncan,Rat.one_mul]
    have hid : ((-F (1-(x+h))-(-F (1-x)))/h-f (1-x)) =
        ((F (1-(x+h))-F (1-x))/(-h)-f (1-x)) := by
      simp only [Rat.div_def,hinv]
      grind only
    rw [hid]
    exact he

theorem reflected_polynomial_hasIntegral (c : Coeffs) (N : Nat) {a b : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    HasIntegral (FunctionOnInterval.exactRat (fun x => taylorDerivativePrefix c N (1-x)) a b)
      (RealRaw.ofRat (integratedTaylorPrefix c N (1-a)-integratedTaylorPrefix c N (1-b))) := by
  let D := reflectedSecant (integratedTaylorPrefixSecantBound 2 c (by decide) N)
  have horder : ExactCellOrderPreservation (fun x => taylorDerivativePrefix c N (1-x))
      (fun u v => -integratedTaylorPrefix c N (1-v)-(-integratedTaylorPrefix c N (1-u))) a b :=
    { lower_const := fun hu huv hv hf => D.exactCellOrder.lower_const (Rat.le_trans ha hu) huv (Rat.le_trans hv hb) hf
      upper_const := fun hu huv hv hf => D.exactCellOrder.upper_const (Rat.le_trans ha hu) huv (Rat.le_trans hv hb) hf }
  have ht := lipschitz_tight (fun x => taylorDerivativePrefix c N (1-x)) a b (polynomialLip c N)
    hab (polynomialLip_nonneg c N) (by
      intro x y hax hxy hyb
      have h := polynomial_lipschitz c N (x := 1-y) (y := 1-x) (by grind) (by grind) (by grind)
      rw [polynomial_prefix,polynomial_prefix] at h
      have he : qabs (taylorDerivativePrefix c N (1-y)-taylorDerivativePrefix c N (1-x)) =
          qabs (taylorDerivativePrefix c N (1-x)-taylorDerivativePrefix c N (1-y)) := by
        rw [show taylorDerivativePrefix c N (1-y)-taylorDerivativePrefix c N (1-x)=
          -(taylorDerivativePrefix c N (1-x)-taylorDerivativePrefix c N (1-y)) by grind only,qabs_neg]
      rw [he]
      have hr : (1-x)-(1-y)=y-x := by grind only
      rw [hr] at h
      exact h)
  have h := horder.hasIntegral ht
  rw [show -integratedTaylorPrefix c N (1-b)-(-integratedTaylorPrefix c N (1-a)) =
      integratedTaylorPrefix c N (1-a)-integratedTaylorPrefix c N (1-b) by grind only] at h
  exact h

end ComputableAnalysis.FormalPowerSeries
