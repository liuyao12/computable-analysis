import ComputableAnalysis.ModularForms.TauNormalizedDifferential

/-! Invariant actual weight-two nome values and exact cusp normalization. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauLambertValue_congr (q w : Scalar) (hq : tauEulerNomeDomain q)
    (hw : tauEulerNomeDomain w) (he : q.val.Equiv w.val) :
    (tauLambertValue q hq).val.Equiv (tauLambertValue w hw).val :=
  weightedLambertSum_congr q w (1/1024) (1/1024) 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw)
    (by decide +kernel) (by decide +kernel) he

def tauWeightTwoNomeMap : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval := tauWeightTwoNomeValue
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr q w hq hw he := FunctionTheory.sub_congr (equiv_refl _ (ofQComplex_valid _))
    (scaleRat_equiv (tauLambertValue_congr q w hq hw he))

theorem tauLambertValue_at_zero (q : Scalar) (hq : tauEulerNomeDomain q) (hz : q.val.Equiv zero) :
    (tauLambertValue q hq).val.Equiv zero := by
  have hq0 : Small q.val 0 := Small.congr (ofQComplex_valid _) q.property (equiv_symm hz) (Small.zero Rat.le_refl)
  let Z : Scalar := ⟨weightedLambertSum q 0 1 Rat.le_refl (by decide +kernel) hq0,
    weightedLambertSum_valid q 0 1 Rat.le_refl (by decide +kernel) hq0 (by decide +kernel)⟩
  have he := weightedLambertSum_congr q q (1/1024) 0 1 (by decide +kernel) Rat.le_refl
    (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq) hq0
    (by decide +kernel) (by decide +kernel) (equiv_refl _ q.property)
  have hb : Small Z.val 0 := by
    simpa only [Rat.mul_zero] using weightedLambertSum_bound q 0 1 Rat.le_refl
      (by decide +kernel) hq0 (by decide +kernel)
  have hs : Small (sub Z.val zero) 0 := by
    simpa only [Rat.add_zero] using SeriesLimitLaws.small_sub hb (Small.zero (Rat.le_refl : (0:Rat)≤0))
  exact equiv_trans (tauLambertValue q hq).property Z.property (ofQComplex_valid _) he
    (SeriesLimitLaws.equiv_of_small_sub_zero _ _ hs)

/-- Exact cusp value of the constructed weight-two Fourier expression. -/
theorem tauWeightTwoNomeValue_at_zero (q : Scalar) (hq : tauEulerNomeDomain q) (hz : q.val.Equiv zero) :
    (tauWeightTwoNomeValue q hq).val.Equiv one := by
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (tauLambertValue q hq).property)
    (hright := ofQComplex_valid _) (tauLambertValue_at_zero q hq hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (tauWeightTwoNomeValue q hq).property)
    (hright := ofQComplex_valid _)
  let l := ComplexRawQuotient.ofRaw (tauLambertValue q hq).val (tauLambertValue q hq).property
  change l=0 at hl
  change 1-ComplexRawQuotient.scaleRat 24 l=1
  rw [hl]
  have hs := ComplexRawQuotient.scaleRat_zero (24:Rat)
  have hz1 : (1:ComplexRawQuotient.Value)-0=1 := by grind only
  exact Eq.mpr (congrArg (fun x => (1:ComplexRawQuotient.Value)-x=1) hs) hz1

end ComputableAnalysis.ModularForms
