import ComputableAnalysis.ModularForms.TauWeightedLambertDerivativeMaps
import ComputableAnalysis.ModularForms.TauWeightedLambertUniformRemainder

/-! Actual infinite higher Lambert values and justified first-order remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem ratio_local (k : Nat) (hk : k≤5) : weightedLambertRatio (1/1024) k≤(1:Rat)/2 := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k <;> decide +kernel

def tauHigherLambertValue (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) : Scalar :=
  ⟨weightedLambertSum q (1/1024) k (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq),
    weightedLambertSum_valid q (1/1024) k (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) (ratio_local k hk)⟩

def tauHigherLambertTail (k N : Nat) : Rat := 4*(8*(1/1024:Rat))*(weightedLambertRatio (1/1024) k)^N

theorem tauHigherLambertValue_close_prefix (q : Scalar) (hq : tauEulerNomeDomain q) (k : Nat) (hk : k≤5) (N : Nat) :
    Small (sub (tauHigherLambertValue q hq k hk).val ((tauLambertPrefixMap k N).eval q hq).val)
      (tauHigherLambertTail k N) :=
  weightedLambertSum_close q (1/1024) k (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (ratio_local k hk) N

/-- Value and derivative convergence control the complete first-order remainder. -/
theorem tauHigherLambertRemainder_close_prefix (k : Nat) (hk : k≤5) (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub
      (SeriesLimitLaws.remainder (tauHigherLambertValue z hz k hk).val (tauHigherLambertValue a ha k hk).val
        (tauWeightedLambertSlopeValue a ha k hk).val (sub z.val a.val))
      (SeriesLimitLaws.remainder ((tauLambertPrefixMap k N).eval z hz).val
        ((tauLambertPrefixMap k N).eval a ha).val
        ((tauLambertPrefixMap_holomorphic k N).derivative a ha).val (sub z.val a.val)))
      (tauHigherLambertTail k N+tauHigherLambertTail k N+2*(128*(weightedSlopeRatio k)^N)*H) := by
  exact SeriesLimitLaws.remainder_close _ _ _ _ _ _ _
    (tauHigherLambertValue z hz k hk).property (tauHigherLambertValue a ha k hk).property
    (tauWeightedLambertSlopeValue a ha k hk).property ((tauLambertPrefixMap k N).eval z hz).property
    ((tauLambertPrefixMap k N).eval a ha).property
    ((tauLambertPrefixMap_holomorphic k N).derivative a ha).property (sub_valid z.property a.property)
    (tauHigherLambertTail k N) (tauHigherLambertTail k N) (128*(weightedSlopeRatio k)^N) H
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (Rat.mul_nonneg (Rat.pow_nonneg (by decide +kernel)) (by decide +kernel)))) hH
    (tauHigherLambertValue_close_prefix z hz k hk N) (tauHigherLambertValue_close_prefix a ha k hk N)
    (tauWeightedLambertSlopeValue_close_actual_derivative a ha k hk N) hd

/-- The remainder comparison error shrinks at every supplied displacement bound. -/
theorem tauHigherLambertRemainder_prefix_error_shrinks (k : Nat) (hk : k≤5) (H : Rat) (hH : 0≤H) :
    ShrinksToZero (fun N => tauHigherLambertTail k N+tauHigherLambertTail k N+2*(128*(weightedSlopeRatio k)^N)*H) := by
  have hv : ShrinksToZero (tauHigherLambertTail k) :=
    weightedLambertSum_tail_shrinks (1/1024) k (by decide +kernel) (ratio_local k hk)
  have hd := SeriesLimitLaws.shrinks_scale _ (tauWeightedLambertSlopeSeries_tail_shrinks k hk) (2*H)
    (Rat.mul_nonneg (by decide +kernel) hH)
  have hs := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ hv hv) hd
  have he : (fun N => (tauHigherLambertTail k N+tauHigherLambertTail k N)+(2*H)*(128*(weightedSlopeRatio k)^N))=
      (fun N => tauHigherLambertTail k N+tauHigherLambertTail k N+2*(128*(weightedSlopeRatio k)^N)*H) := by
    funext N
    grind only
  rw [he] at hs
  exact hs

theorem tauHigherLambertValue_remainder_bound (k : Nat) (hk : k≤5) (a z : Scalar) (ha : tauEulerNomeDomain a)
    (hz : tauEulerNomeDomain z) (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder (tauHigherLambertValue z hz k hk).val (tauHigherLambertValue a ha k hk).val
      (tauWeightedLambertSlopeValue a ha k hk).val (sub z.val a.val)) ((4096+67584*2^k)*H^2) := by
  apply SeriesLimitLaws.small_of_prefix_bound _
    (SeriesLimitLaws.remainder_valid _ _ _ _ (tauHigherLambertValue z hz k hk).property
      (tauHigherLambertValue a ha k hk).property (tauWeightedLambertSlopeValue a ha k hk).property (sub_valid z.property a.property))
    (fun N => SeriesLimitLaws.remainder ((tauLambertPrefixMap k N).eval z hz).val
      ((tauLambertPrefixMap k N).eval a ha).val
      ((tauLambertPrefixMap_holomorphic k N).derivative a ha).val (sub z.val a.val))
    (fun N => SeriesLimitLaws.remainder_valid _ _ _ _ ((tauLambertPrefixMap k N).eval z hz).property
      ((tauLambertPrefixMap k N).eval a ha).property
      ((tauLambertPrefixMap_holomorphic k N).derivative a ha).property (sub_valid z.property a.property))
    ((4096+67584*2^k)*H^2) _ (tauHigherLambertRemainder_prefix_error_shrinks k hk H hH)
    (fun N => tauHigherLambertRemainder_close_prefix k hk a z ha hz H hH hd N)
    (fun N => tauWeightedLambertPrefix_uniform_remainder_bound k hk a z ha hz H hH hd N)

end ComputableAnalysis.ModularForms
