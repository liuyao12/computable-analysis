import ComputableAnalysis.RiemannHilbert.CenteredSeriesEstimates

/-! Quantitative comparison of actual represented power-series values.
Coefficient errors with a geometric majorant give a value error by finite
products, geometric sums and shrinking tails, without an assumed sum law. -/
namespace ComputableAnalysis.RiemannHilbert.CoefficientSeriesComparison
open ComplexRaw FunctionTheory LocalODE BoundedSeries
set_option autoImplicit false

theorem prefix_difference (c d : Nat → ComplexRaw) (hc : ∀ j, (c j).Valid)
    (hd : ∀ j, (d j).Valid) (z : ComplexRaw) (hz : z.Valid) (N : Nat) :
    (sub (valueBlock c z 0 N) (valueBlock d z 0 N)).Equiv
      (valueBlock (fun j => sub (c j) (d j)) z 0 N) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (valueBlock_valid c z hc hz 0 N) (valueBlock_valid d z hd hz 0 N))
    (hright := valueBlock_valid _ z (fun j => sub_valid (hc j) (hd j)) hz 0 N)
  induction N with
  | zero => change (0:ScalarAlgebra.Value)-0=0; grind only
  | succ N ih =>
    change ComplexRawQuotient.ofRaw (valueBlock c z 0 N) (valueBlock_valid c z hc hz 0 N)-
      ComplexRawQuotient.ofRaw (valueBlock d z 0 N) (valueBlock_valid d z hd hz 0 N)=
      ComplexRawQuotient.ofRaw (valueBlock (fun j => sub (c j) (d j)) z 0 N)
        (valueBlock_valid _ z (fun j => sub_valid (hc j) (hd j)) hz 0 N) at ih
    simp only [valueBlock,Nat.zero_add]
    change (ComplexRawQuotient.ofRaw (valueBlock c z 0 N) (valueBlock_valid c z hc hz 0 N)+
        ComplexRawQuotient.ofRaw (c N) (hc N)*ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N))-
      (ComplexRawQuotient.ofRaw (valueBlock d z 0 N) (valueBlock_valid d z hd hz 0 N)+
        ComplexRawQuotient.ofRaw (d N) (hd N)*ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N))=
      ComplexRawQuotient.ofRaw (valueBlock (fun j => sub (c j) (d j)) z 0 N)
        (valueBlock_valid _ z (fun j => sub_valid (hc j) (hd j)) hz 0 N)+
      (ComplexRawQuotient.ofRaw (c N) (hc N)-ComplexRawQuotient.ofRaw (d N) (hd N))*
        ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N)
    grind only

theorem value_difference (c d : Nat → ComplexRaw) (hc : ∀ j, (c j).Valid)
    (hd : ∀ j, (d j).Valid) (z : ComplexRaw) (hz : z.Valid)
    (C D K R E : Rat) (hC : 0≤C) (hD : 0≤D) (hK : 0≤K) (hR : 0≤R) (hE : 0≤E)
    (bc : ∀ j, Small (c j) (C*K^j)) (bd : ∀ j, Small (d j) (D*K^j))
    (be : ∀ j, Small (sub (c j) (d j)) (E*K^j)) (bz : Small z R)
    (hl : 2*K*R≤(1:Rat)/2) :
    Small (sub (sumValue c z hc hz C K R) (sumValue d z hd hz D K R)) (4*E) := by
  have hq : 0≤2*K*R := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hK) hR
  apply SeriesLimitLaws.small_of_prefix_bound _
    (sub_valid (sumValue_valid c z hc hz C K R hC hK hR bc bz hl)
      (sumValue_valid d z hd hz D K R hD hK hR bd bz hl))
    (fun N => sub (valueBlock c z 0 N) (valueBlock d z 0 N))
    (fun N => sub_valid (valueBlock_valid c z hc hz 0 N) (valueBlock_valid d z hd hz 0 N))
    (4*E) (fun N => valueTail C K R N+valueTail D K R N)
    (RepresentedCauchySum.sum_shrinks _ _ (tail_bound_shrinks C (2*K*R) hC hq hl)
      (tail_bound_shrinks D (2*K*R) hD hq hl))
  · intro N
    exact SeriesLimitLaws.difference_close _ _ _ _
      (sumValue_valid c z hc hz C K R hC hK hR bc bz hl)
      (sumValue_valid d z hd hz D K R hD hK hR bd bz hl)
      (valueBlock_valid c z hc hz 0 N) (valueBlock_valid d z hd hz 0 N) _ _
      (sumValue_close_prefix c z hc hz C K R hC hK hR bc bz hl N)
      (sumValue_close_prefix d z hd hz D K R hD hK hR bd bz hl N)
  · intro N
    have hs := ScalarSeries.block_bound (seriesTerm (fun j => sub (c j) (d j)) z) E (2*K*R)
      hE hq hl (seriesTerm_bound _ z (fun j => sub_valid (hc j) (hd j)) hz E K R hE hK hR be bz) 0 N
    rw [←valueBlock_as_terms] at hs
    simp only [Rat.pow_zero,Rat.mul_one] at hs
    exact Small.congr (valueBlock_valid _ z (fun j => sub_valid (hc j) (hd j)) hz 0 N)
      (sub_valid (valueBlock_valid c z hc hz 0 N) (valueBlock_valid d z hd hz 0 N))
      (equiv_symm (prefix_difference c d hc hd z hz N)) hs

end ComputableAnalysis.RiemannHilbert.CoefficientSeriesComparison
