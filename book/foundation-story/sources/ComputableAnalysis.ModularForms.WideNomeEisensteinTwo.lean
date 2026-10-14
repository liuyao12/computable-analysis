import ComputableAnalysis.ModularForms.WideLambertFirstHolomorphic
import ComputableAnalysis.ModularForms.TauWeightTwoHolomorphic
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Actual normalized weight-two Eisenstein nome evaluator on the wider disk. -/
def wideNomeEisensteinTwoMap : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q hq := ⟨add one (scaleRat (-24) (wideLambertFirstMap.eval q hq).val),
    add_valid (ofQComplex_valid _) (scaleRat_valid (wideLambertFirstMap.eval q hq).property)⟩
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w hq hw he := add_equiv (equiv_refl _ (ofQComplex_valid _))
    (scaleRat_equiv (wideLambertFirstMap.eval_congr q w hq hw he))

noncomputable def wideNomeEisensteinTwoMap_holomorphic : Holomorphic wideNomeEisensteinTwoMap := by
  let C : Scalar := ⟨scaleRat (-24) one,scaleRat_valid (ofQComplex_valid _)⟩
  let hc := constantOn_holomorphic wideLambertFifthDomain_openData C
  let ho := constantOn_holomorphic wideLambertFifthDomain_openData oneScalar
  let hp := hc.productOn wideLambertFirstMap_holomorphic (fun _ h => h)
  exact (ho.sumOn hp (fun _ h => h)).transfer wideNomeEisensteinTwoMap (fun _ h => h)
    ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
    (fun q hq => by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((sumOn (constantOn wideLambertFifthDomain wideLambertFifthDomain_openData.invariant oneScalar)
          (productOn (constantOn wideLambertFifthDomain wideLambertFifthDomain_openData.invariant C)
            wideLambertFirstMap (fun _ h => h)) (fun _ h => h)).eval q hq).property)
        (hright := (wideNomeEisensteinTwoMap.eval q hq).property)
      let L := ComplexRawQuotient.ofRaw (wideLambertFirstMap.eval q hq).val (wideLambertFirstMap.eval q hq).property
      change 1+ComplexRawQuotient.scaleRat (-24) 1*L=1+ComplexRawQuotient.scaleRat (-24) L
      rw [←ComplexRawQuotient.scaleRat_mul]
      congr 1
      congr 1
      grind only)

/-- Exact agreement with the original actual normalized Eisenstein nome evaluator. -/
theorem wideNomeEisensteinTwoMap_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (wideNomeEisensteinTwoMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv
      (tauWeightTwoNomeMap.eval q hq).val := by
  have h := wideLambertFirstMap_tau_agreement q hq
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (wideLambertFirstMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).property)
    (hright := (tauHigherLambertValue q hq 1 (by omega)).property) h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (wideNomeEisensteinTwoMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).property)
    (hright := (tauWeightTwoNomeMap.eval q hq).property)
  let L := ComplexRawQuotient.ofRaw
    (wideLambertFirstMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val
    (wideLambertFirstMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).property
  let l := ComplexRawQuotient.ofRaw (tauHigherLambertValue q hq 1 (by omega)).val
    (tauHigherLambertValue q hq 1 (by omega)).property
  change L=l at he
  change 1+ComplexRawQuotient.scaleRat (-24) L=1-ComplexRawQuotient.scaleRat 24 l
  rw [he,←ComplexRawQuotient.neg_scaleRat]
  rfl
end ComputableAnalysis.ModularForms
