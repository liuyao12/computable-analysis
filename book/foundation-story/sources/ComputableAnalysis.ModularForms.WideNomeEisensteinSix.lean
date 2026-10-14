import ComputableAnalysis.ModularForms.WideLambertFifthHolomorphic
import ComputableAnalysis.ModularForms.NomeEisensteinHolomorphic
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Actual normalized weight-six Eisenstein nome evaluator on the wider disk. -/
def wideNomeEisensteinSixMap : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q hq := ⟨add one (scaleRat (-504) (wideLambertFifthMap.eval q hq).val),
    add_valid (ofQComplex_valid _) (scaleRat_valid (wideLambertFifthMap.eval q hq).property)⟩
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w hq hw he := add_equiv (equiv_refl _ (ofQComplex_valid _))
    (scaleRat_equiv (wideLambertFifthMap.eval_congr q w hq hw he))

noncomputable def wideNomeEisensteinSixMap_holomorphic : Holomorphic wideNomeEisensteinSixMap := by
  let C : Scalar := ⟨scaleRat (-504) one,scaleRat_valid (ofQComplex_valid _)⟩
  let hc := constantOn_holomorphic wideLambertFifthDomain_openData C
  let ho := constantOn_holomorphic wideLambertFifthDomain_openData oneScalar
  let hp := hc.productOn wideLambertFifthMap_holomorphic (fun _ h => h)
  exact (ho.sumOn hp (fun _ h => h)).transfer wideNomeEisensteinSixMap (fun _ h => h)
    ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
    (fun q hq => by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((sumOn (constantOn wideLambertFifthDomain wideLambertFifthDomain_openData.invariant oneScalar)
          (productOn (constantOn wideLambertFifthDomain wideLambertFifthDomain_openData.invariant C)
            wideLambertFifthMap (fun _ h => h)) (fun _ h => h)).eval q hq).property)
        (hright := (wideNomeEisensteinSixMap.eval q hq).property)
      let L := ComplexRawQuotient.ofRaw (wideLambertFifthMap.eval q hq).val (wideLambertFifthMap.eval q hq).property
      change 1+ComplexRawQuotient.scaleRat (-504) 1*L=1+ComplexRawQuotient.scaleRat (-504) L
      rw [←ComplexRawQuotient.scaleRat_mul]
      congr 1
      congr 1
      grind only)

/-- Exact agreement with the original actual normalized Eisenstein nome evaluator. -/
theorem wideNomeEisensteinSixMap_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (wideNomeEisensteinSixMap.eval q (tauEulerNomeDomain_wide_fifth_mem q hq)).val.Equiv
      (nomeEisensteinSixMap.eval q hq).val :=
  add_equiv (equiv_refl _ (ofQComplex_valid _)) (scaleRat_equiv (wideLambertFifthMap_tau_agreement q hq))
end ComputableAnalysis.ModularForms
