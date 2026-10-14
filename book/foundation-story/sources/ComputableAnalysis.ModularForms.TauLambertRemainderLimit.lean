import ComputableAnalysis.ModularForms.TauLambertDerivativeMaps

/-! Quantitative convergence of actual Lambert first-order remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Value and derivative convergence control the complete first-order remainder. -/
theorem tauLambertRemainder_close_prefix (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub
      (SeriesLimitLaws.remainder (tauLambertValue z hz).val (tauLambertValue a ha).val
        (tauLambertSlopeValue a ha).val (sub z.val a.val))
      (SeriesLimitLaws.remainder ((tauLambertPrefixMap 1 N).eval z hz).val
        ((tauLambertPrefixMap 1 N).eval a ha).val
        ((tauLambertPrefixMap_holomorphic 1 N).derivative a ha).val (sub z.val a.val)))
      (tauLambertTail N+tauLambertTail N+2*(128*(1/128:Rat)^N)*H) := by
  exact SeriesLimitLaws.remainder_close _ _ _ _ _ _ _
    (tauLambertValue z hz).property (tauLambertValue a ha).property
    (tauLambertSlopeValue a ha).property ((tauLambertPrefixMap 1 N).eval z hz).property
    ((tauLambertPrefixMap 1 N).eval a ha).property
    ((tauLambertPrefixMap_holomorphic 1 N).derivative a ha).property (sub_valid z.property a.property)
    (tauLambertTail N) (tauLambertTail N) (128*(1/128:Rat)^N) H
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))) hH
    (tauLambertNomeMap_close_prefix z hz N) (tauLambertNomeMap_close_prefix a ha N)
    (tauLambertSlopeValue_close_actual_derivative a ha N) hd

/-- The remainder comparison error shrinks at every supplied displacement bound. -/
theorem tauLambertRemainder_prefix_error_shrinks (H : Rat) (hH : 0≤H) :
    ShrinksToZero (fun N => tauLambertTail N+tauLambertTail N+2*(128*(1/128:Rat)^N)*H) := by
  have hv : ShrinksToZero tauLambertTail :=
    weightedLambertSum_tail_shrinks (1/1024) 1 (by decide +kernel) (by decide +kernel)
  have hd := SeriesLimitLaws.shrinks_scale _ tauLambertSlopeSeries_tail_shrinks (2*H)
    (Rat.mul_nonneg (by decide +kernel) hH)
  have hs := RepresentedCauchySum.sum_shrinks _ _
    (RepresentedCauchySum.sum_shrinks _ _ hv hv) hd
  have he : (fun N => (tauLambertTail N+tauLambertTail N)+(2*H)*(128*(1/128:Rat)^N))=
      (fun N => tauLambertTail N+tauLambertTail N+2*(128*(1/128:Rat)^N)*H) := by
    funext N
    grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.ModularForms
