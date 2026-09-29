import ComputableAnalysis.GeometricIntegral

/-! A finite polynomial integral inherits a uniform rational difference bound. -/
namespace ComputableAnalysis.BinomialPower
open FormalPowerSeries Integral FinitePolynomial

theorem polynomial_integral_bound (c d : Coeffs) (n m : Nat) {a b e : Rat}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (he : ∀ x, a ≤ x → x ≤ b →
      qabs (sumBelow (fun k => c k*x^k) n-sumBelow (fun k => d k*x^k) m) ≤ e) :
    qabs ((integratedTaylorPrefix c n b-integratedTaylorPrefix c n a)-
      (integratedTaylorPrefix d m b-integratedTaylorPrefix d m a)) ≤ (b-a)*e := by
  let D := (integratedTaylorPrefixSecantBound 1 c (by decide) n).add
    ((integratedTaylorPrefixSecantBound 1 d (by decide) m).scaleRat (-1))
  have hlo := D.exactCellOrder.lower_const (c := -e) ha hab hb (by
    intro x hx hy
    have h := he x hx hy
    have hn := neg_qabs_le_self (sumBelow (fun k => c k*x^k) n-sumBelow (fun k => d k*x^k) m)
    rw [polynomial_prefix,polynomial_prefix] at h hn
    change -e ≤ taylorDerivativePrefix c n x+(-1)*taylorDerivativePrefix d m x
    grind only)
  have hhi := D.exactCellOrder.upper_const (c := e) ha hab hb (by
    intro x hx hy
    have h := he x hx hy
    have hn := self_le_qabs (sumBelow (fun k => c k*x^k) n-sumBelow (fun k => d k*x^k) m)
    rw [polynomial_prefix,polynomial_prefix] at h hn
    change taylorDerivativePrefix c n x+(-1)*taylorDerivativePrefix d m x ≤ e
    grind only)
  change (b-a)*(-e) ≤ (integratedTaylorPrefix c n b+(-1)*integratedTaylorPrefix d m b)-
    (integratedTaylorPrefix c n a+(-1)*integratedTaylorPrefix d m a) at hlo
  change (integratedTaylorPrefix c n b+(-1)*integratedTaylorPrefix d m b)-
    (integratedTaylorPrefix c n a+(-1)*integratedTaylorPrefix d m a) ≤ (b-a)*e at hhi
  apply qabs_le_of_neg_le_le <;> grind only

end ComputableAnalysis.BinomialPower
