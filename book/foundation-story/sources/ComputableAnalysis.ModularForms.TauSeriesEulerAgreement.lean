import ComputableAnalysis.ModularForms.TauSeriesValue

/-! Agreement of the ordinary tau series with the actual Euler product. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

/-- Stable ordinary prefixes agree with the actual finite-product coefficients. -/
theorem tauSeriesPrefix_finite_coefficients (q : Scalar) (N K : Nat) (hK : K≤N+1) :
    (integerCoefficientPrefix (discriminantProduct N) q K).val.Equiv (tauSeriesPrefix q K).val := by
  induction K with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ K ih =>
    have hc : discriminantProduct N K=tau (K+1) := (tau_eq_finiteProduct K N (by omega)).symm
    have ht : (scaleRat (discriminantProduct N K:Rat) (LocalODE.power q.val K)).Equiv
        (scaleRat (tau (K+1):Rat) (LocalODE.power q.val K)) := by
      rw [hc]
      exact equiv_refl _ (scaleRat_valid (LocalODE.power_valid _ q.property K))
    exact add_equiv (ih (by omega)) ht

private theorem degree_bound (N : Nat) : N≤discriminantProductDegree N+1 := by
  induction N with
  | zero => omega
  | succ N ih => simp only [discriminantProductDegree]; omega

/-- A finite Euler product is close to the stable ordinary tau prefix. -/
theorem finiteDiscriminantEulerProduct_close_tau_prefix (q : Scalar)
    (hq : Small q.val (1/1024)) (N : Nat) :
    Small (sub (finiteDiscriminantEulerProduct q N).val (tauSeriesPrefix q N).val) (tauSeriesTail N) := by
  let L := discriminantProductDegree N+1
  have h := discriminantProduct_complex_tail q hq N N (L-N)
  have he : N+(L-N)=L := by have := degree_bound N; dsimp [L]; omega
  rw [he] at h
  exact Small.congr
    (sub_valid (integerCoefficientPrefix _ q L).property (integerCoefficientPrefix _ q N).property)
    (sub_valid (finiteDiscriminantEulerProduct q N).property (tauSeriesPrefix q N).property)
    (FunctionTheory.sub_congr (discriminantProduct_exact_evaluation q N)
      (tauSeriesPrefix_finite_coefficients q N N (by omega))) h

private theorem small_triangle (a b c : Scalar) (R S : Rat)
    (hab : Small (sub a.val b.val) R) (hbc : Small (sub b.val c.val) S) :
    Small (sub a.val c.val) (R+S) := by
  have he : (add (sub a.val b.val) (sub b.val c.val)).Equiv (sub a.val c.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid a.property b.property) (sub_valid b.property c.property))
      (hright := sub_valid a.property c.property)
    let A := ComplexRawQuotient.ofRaw a.val a.property
    let B := ComplexRawQuotient.ofRaw b.val b.property
    let C := ComplexRawQuotient.ofRaw c.val c.property
    change (A-B)+(B-C)=A-C
    grind only
  exact Small.congr (add_valid (sub_valid a.property b.property) (sub_valid b.property c.property))
    (sub_valid a.property c.property) he (LocalODE.small_add hab hbc)

/-- The constructed ordinary tau-series sum equals the actual Euler product. -/
theorem tauSeriesValue_euler_agreement (q : Scalar) (hq : Small q.val (1/1024)) :
    (tauSeriesValue q hq).val.Equiv
      (tauEulerProduct q (1/1024) (by decide +kernel) Rat.le_refl hq).val := by
  let S := tauSeriesValue q hq
  let P := tauEulerProduct q (1/1024) (by decide +kernel) Rat.le_refl hq
  let e := fun N => tauSeriesTail N+(tauEulerProductTail (1/1024) N+tauSeriesTail N)
  have he : ShrinksToZero e := RepresentedCauchySum.sum_shrinks _ _ tauSeriesTail_shrinks
    (RepresentedCauchySum.sum_shrinks _ _
      (tauEulerProductTail_shrinks (1/1024) (by decide +kernel) Rat.le_refl) tauSeriesTail_shrinks)
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 e he
  intro N
  have hp := small_triangle P (finiteDiscriminantEulerProduct q N) (tauSeriesPrefix q N) _ _
    (tauEulerProduct_close_prefix q (1/1024) (by decide +kernel) Rat.le_refl hq N)
    (finiteDiscriminantEulerProduct_close_tau_prefix q hq N)
  have hp' := RepresentedCauchySum.small_sub_symm _ _ _ hp
  have hs := small_triangle S (tauSeriesPrefix q N) P _ _
    (tauSeriesValue_close_prefix q hq N) hp'
  simpa only [Rat.zero_add,e,tauEulerProductTail] using hs

/-- Exact tau-series interpretation of the normalized holomorphic Euler map. -/
theorem tauNormalizedEulerMap_series_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (mul (tauSeriesValue q (LocalODE.interior_bound _ q hq)).val q.val).Equiv
      (tauNormalizedEulerMap.eval q hq).val :=
  mul_equiv (tauSeriesValue q (LocalODE.interior_bound _ q hq)).property
    (tauEulerNomeMap.eval q hq).property q.property q.property
    (tauSeriesValue_euler_agreement q (LocalODE.interior_bound _ q hq)) (equiv_refl _ q.property)

end ComputableAnalysis.ModularForms
