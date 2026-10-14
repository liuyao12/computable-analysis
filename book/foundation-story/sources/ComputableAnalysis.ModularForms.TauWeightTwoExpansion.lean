import ComputableAnalysis.ModularForms.TauWeightTwoNomeMap
import ComputableAnalysis.ModularForms.WeightedLambertLeadingTerm

/-! Quantitative first-order expansion of the actual weight-two nome expression. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The fixed-radius Lambert value has a quadratic expansion at every
independently supplied smaller represented input bound. -/
theorem tauLambertValue_linear_bound (q : Scalar) (hq : tauEulerNomeDomain q) (R : Rat)
    (hR : 0≤R) (hRM : R≤(1:Rat)/1024) (hqR : Small q.val R) :
    Small (sub (tauLambertValue q hq).val q.val) (160*R*R) := by
  have hlocal : 4*R≤(1:Rat)/2 := by
    have hm := Rat.mul_le_mul_of_nonneg_left hRM (show (0:Rat)≤4 by decide +kernel)
    exact Rat.le_trans hm (by decide +kernel)
  have hseries : weightedLambertRatio R 1≤(1:Rat)/2 := by
    unfold weightedLambertRatio
    rw [Rat.pow_one]
    grind only
  let W : Scalar := ⟨weightedLambertSum q R 1 hR hlocal hqR,
    weightedLambertSum_valid q R 1 hR hlocal hqR hseries⟩
  have he := weightedLambertSum_congr q q (1/1024) R 1 (by decide +kernel) hR
    (by decide +kernel) hlocal (LocalODE.interior_bound _ q hq) hqR (by decide +kernel) hseries
    (equiv_refl _ q.property)
  have hb := weightedLambertSum_linear_bound q R 1 hR hlocal hqR hseries
  have hc : (64*(2:Rat)^1+32)=160 := by decide +kernel
  rw [hc] at hb
  exact Small.congr (sub_valid W.property q.property)
    (sub_valid (tauLambertValue q hq).property q.property)
    (FunctionTheory.sub_congr (equiv_symm he) (equiv_refl _ q.property)) hb

/-- Actual weight-two values have the expansion one minus 24 times the nome,
with a uniform quadratic error. -/
theorem tauWeightTwoNomeValue_linear_bound (q : Scalar) (hq : tauEulerNomeDomain q) (R : Rat)
    (hR : 0≤R) (hRM : R≤(1:Rat)/1024) (hqR : Small q.val R) :
    Small (sub (tauWeightTwoNomeValue q hq).val (sub one (scaleRat 24 q.val))) (3840*R*R) := by
  let L := tauLambertValue q hq
  have hb := SeriesLimitLaws.small_neg
    (LocalODE.small_scale (show (0:Rat)≤24 by decide +kernel)
      (tauLambertValue_linear_bound q hq R hR hRM hqR))
  have he : (neg (scaleRat 24 (sub L.val q.val))).Equiv
      (sub (tauWeightTwoNomeValue q hq).val (sub one (scaleRat 24 q.val))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (scaleRat_valid (sub_valid L.property q.property)))
      (hright := sub_valid (tauWeightTwoNomeValue q hq).property
        (sub_valid (ofQComplex_valid _) (scaleRat_valid q.property)))
    let l := ComplexRawQuotient.ofRaw L.val L.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change -(ComplexRawQuotient.scaleRat 24 (l+(-Q)))=
      (1-ComplexRawQuotient.scaleRat 24 l)-(1-ComplexRawQuotient.scaleRat 24 Q)
    rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_eq_scaleRat_neg_one Q,
      ComplexRawQuotient.scaleRat_scaleRat,show (24:Rat)*(-1)= -24 by decide +kernel,
      ←ComplexRawQuotient.neg_scaleRat]
    grind only
  have h := Small.congr (neg_valid (scaleRat_valid (sub_valid L.property q.property)))
    (sub_valid (tauWeightTwoNomeValue q hq).property (sub_valid (ofQComplex_valid _) (scaleRat_valid q.property))) he hb
  have hc : (24:Rat)*(160*R*R)=3840*R*R := by grind only
  rw [hc] at h
  exact h

end ComputableAnalysis.ModularForms
