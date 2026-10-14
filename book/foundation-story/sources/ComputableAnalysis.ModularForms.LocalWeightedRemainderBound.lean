import ComputableAnalysis.ModularForms.PairedRiccatiCauchyIntegrand
import ComputableAnalysis.RiemannHilbert.GeometricSeries

/-! Weighted finite local derivative remainders, for the pending analytic
contour-cancellation argument. This does not assert a grid model or formula. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem localWeightedRemainder_bound (f : DomainFunctions.Map) (a d : Scalar)
    (ha : f.domain a) (hf : HasDerivativeAt f a ha d)
    (eps H : QPos) (hH : H.val≤(hf.delta eps).val)
    (z v : Nat → Scalar) (hz : ∀ j, f.domain (z j))
    (hnear : ∀ j, Small (sub (z j).val a.val) H.val)
    (hvel : ∀ j, Small (v j).val H.val) (K : Nat) :
    Small (ScalarSeries.block (fun j => mul
      (remainder f a ha d (z j) (hz j)) (v j).val) 0 K)
      ((K:Rat)*(2*(eps.val*H.val)*H.val)) := by
  have hterm (j : Nat) : Small (mul
      (remainder f a ha d (z j) (hz j)) (v j).val)
      (2*(eps.val*H.val)*H.val) :=
    Small.mul (remainder_valid f a ha d (z j) (hz j)) (v j).property
      (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property))
      (Rat.le_of_lt H.property) (hf.estimate eps H (z j) (hz j) hH (hnear j)) (hvel j)
  induction K with
  | zero =>
    apply Small.zero
    change (0:Rat)≤0*(2*(eps.val*H.val)*H.val)
    rw [Rat.zero_mul]
    exact Rat.le_refl
  | succ K ih =>
    have hb := LocalODE.small_add ih (hterm K)
    have he : (K:Rat)*(2*(eps.val*H.val)*H.val)+2*(eps.val*H.val)*H.val=
        ((K+1:Nat):Rat)*(2*(eps.val*H.val)*H.val) := by
      rw [Rat.natCast_add]
      change _=((K:Rat)+1)*(2*(eps.val*H.val)*H.val)
      grind only
    rw [he] at hb
    simpa only [ScalarSeries.block,Nat.zero_add] using hb

end ComputableAnalysis.ModularForms
