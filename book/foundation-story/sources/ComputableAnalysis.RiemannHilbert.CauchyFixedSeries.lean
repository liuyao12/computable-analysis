import ComputableAnalysis.RiemannHilbert.SampledLimitAgreement
import ComputableAnalysis.RiemannHilbert.GeneralSeriesHolomorphic

/-! The fixed Cauchy moments, rather than stage-dependent quadrature
coefficients, sum to the independently supplied interior function. -/
namespace ComputableAnalysis.RiemannHilbert.CauchyFixedSeries
open ComplexRaw FunctionTheory LocalODE CauchyTaylor
set_option autoImplicit false

theorem rational_disk (q : QComplex) (R : Rat) (_hR : 0 ≤ R)
    (hq : Small (ofQComplex q) R) : InDisk q (2*R) := by
  have hlr := hq.1 0 0
  have hur := hq.2.1 0 0
  have hli := hq.2.2.1 0 0
  have hui := hq.2.2.2 0 0
  change -R ≤ q.re at hlr
  change q.re ≤ R at hur
  change -R ≤ q.im at hli
  change q.im ≤ R at hui
  have hr := Rat.mul_nonneg (show 0 ≤ R-q.re by grind) (show 0 ≤ R+q.re by grind)
  have hi := Rat.mul_nonneg (show 0 ≤ R-q.im by grind) (show 0 ≤ R+q.im by grind)
  have hs := rat_square_nonneg_basic R
  unfold InDisk QComplex.normSq
  grind only

theorem prefix_error {F : QComplex → ComplexRaw} (c : SeriesCertificate F)
    (q : QComplex) (r : Rat) (hr : 0 ≤ r) (hr1 : r < 1) (hq : InDisk q r) (N : Nat) :
    Small (sub (F q) (c.moments.partialSum q N))
      (4*(c.cauchy.massBound*(1-r)⁻¹)*r^N) := by
  apply SampledLimitAgreement.bound (F q) (c.moments.partialSum q N)
    (c.cauchy.valid q r hr hr1 hq) (c.moments.partialSum_valid q N)
    (fun n => cauchySample (c.cauchy.rules n) q)
    (fun n => polynomialSample (c.cauchy.rules n) q N)
    (4*(c.cauchy.massBound*(1-r)⁻¹)*r^N)
    (CertifiedComplexApproximation.rate (c.cauchy.quadratureBound r))
    (CertifiedComplexApproximation.rate_nonneg (c.cauchy.quadrature_nonneg r))
    (CertifiedComplexApproximation.rate_shrinks _)
    (c.cauchy.encloses q r hr hr1 hq) (c.moments.partialSum_contains_sample q N)
  intro n
  have hi : 0 ≤ (1-r)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 (by grind))
  have ht : 0 ≤ 2*(r^N*(1-r)⁻¹) := Rat.mul_nonneg (by decide) (Rat.mul_nonneg (Rat.pow_nonneg hr) hi)
  have hm := Rat.mul_le_mul_of_nonneg_right (c.cauchy.mass_le n) ht
  have hs := Rat.mul_nonneg (Rat.mul_nonneg c.cauchy.mass_nonneg hi) (Rat.pow_nonneg (n := N) hr)
  have hb := rule_remainder hr hr1 hq (c.cauchy.rules n) N
  grind only

theorem rational_agreement {F : QComplex → ComplexRaw} (c : SeriesCertificate F)
    (q : QComplex) (R : Rat) (hR : 0 ≤ R) (hl : 8*R ≤ (1 : Rat)/2)
    (hq : Small (ofQComplex q) R) :
    (F q).Equiv (BoundedSeries.sumValue c.coefficient (ofQComplex q)
      c.moments.coefficient_valid (ofQComplex_valid _) (2*c.cauchy.massBound) 1 R) := by
  let C := 2*c.cauchy.massBound
  let r := 2*R
  have hC : 0 ≤ C := Rat.mul_nonneg (by decide) c.cauchy.mass_nonneg
  have hr : 0 ≤ r := Rat.mul_nonneg (by decide) hR
  have hrhalf : r ≤ (1 : Rat)/2 := by dsimp [r]; grind only
  have hr1 : r < 1 := by grind only
  have hqr := rational_disk q R hR hq
  have hb := CauchyMoments.certificate_bound c
  have hvLocal : 2*1*R ≤ (1 : Rat)/2 := by grind only
  let v := BoundedSeries.sumValue c.coefficient (ofQComplex q)
    c.moments.coefficient_valid (ofQComplex_valid _) C 1 R
  have hf := c.cauchy.valid q r hr hr1 hqr
  have hv := BoundedSeries.sumValue_valid c.coefficient (ofQComplex q)
    c.moments.coefficient_valid (ofQComplex_valid _) C 1 R hC (by decide) hR hb hq hvLocal
  let e := fun N => 4*(c.cauchy.massBound*(1-r)⁻¹)*r^N + valueTail C 1 R N
  have hi : 0 ≤ (1-r)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 (by grind only))
  have he := RepresentedCauchySum.sum_shrinks _ _
    (tail_bound_shrinks (c.cauchy.massBound*(1-r)⁻¹) r
      (Rat.mul_nonneg c.cauchy.mass_nonneg hi) hr hrhalf)
    (tail_bound_shrinks C (2*1*R) hC (by grind only) hvLocal)
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 e he
  intro N
  let p := BoundedSeries.valueBlock c.coefficient (ofQComplex q) 0 N
  have hp := BoundedSeries.valueBlock_valid c.coefficient (ofQComplex q)
    c.moments.coefficient_valid (ofQComplex_valid _) 0 N
  have hfp := Small.congr (sub_valid hf (c.moments.partialSum_valid q N)) (sub_valid hf hp)
    (FunctionTheory.sub_congr (equiv_refl _ hf) (equiv_symm (CauchyMoments.rational_prefix c.moments q N)))
    (prefix_error c q r hr hr1 hqr N)
  have hvp := BoundedSeries.sumValue_close_prefix c.coefficient (ofQComplex q)
    c.moments.coefficient_valid (ofQComplex_valid _) C 1 R hC (by decide) hR hb hq hvLocal N
  have hs := SeriesLimitLaws.small_sub hfp hvp
  have hi : (sub (sub (F q) p) (sub v p)).Equiv (sub (F q) v) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid hf hp) (sub_valid hv hp)) (hright := sub_valid hf hv)
    let A := ComplexRawQuotient.ofRaw (F q) hf
    let B := ComplexRawQuotient.ofRaw v hv
    let P := ComplexRawQuotient.ofRaw p hp
    change (A-P)-(B-P)=A-B
    grind
  exact Small.congr (sub_valid (sub_valid hf hp) (sub_valid hv hp)) (sub_valid hf hv) hi
    (hs.mono (by change e N ≤ 0+e N; rw [Rat.zero_add]; exact Rat.le_refl))

end ComputableAnalysis.RiemannHilbert.CauchyFixedSeries
