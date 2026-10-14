import ComputableAnalysis.ModularForms.TauLambertHolomorphic

/-! Actual holomorphicity of the weight-two nome expression. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

noncomputable def tauWeightTwoNomeMap_holomorphic : Holomorphic tauWeightTwoNomeMap := by
  let c : Scalar := ⟨scaleRat (-24) one, scaleRat_valid (ofQComplex_valid _)⟩
  let hc := constantOn_holomorphic tauEulerNomeDomain_openData c
  let ho := constantOn_holomorphic tauEulerNomeDomain_openData oneScalar
  let hp := hc.productOn tauLambertNomeMap_holomorphic (fun _ h => h)
  exact (ho.sumOn hp (fun _ h => h)).transfer tauWeightTwoNomeMap (fun _ h => h)
    ⟨tauEulerNomeDomain_openData.radius,tauEulerNomeDomain_openData.inside⟩
    (fun q hq => by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((sumOn (constantOn tauEulerNomeDomain tauEulerNomeDomain_openData.invariant oneScalar)
          (productOn (constantOn tauEulerNomeDomain tauEulerNomeDomain_openData.invariant c)
            tauLambertNomeMap (fun _ h => h)) (fun _ h => h)).eval q hq).property)
        (hright := (tauWeightTwoNomeMap.eval q hq).property)
      let L := ComplexRawQuotient.ofRaw (tauLambertValue q hq).val (tauLambertValue q hq).property
      change 1+ComplexRawQuotient.scaleRat (-24) 1*L=1-ComplexRawQuotient.scaleRat 24 L
      rw [←ComplexRawQuotient.scaleRat_mul]
      have hm : (1:ComplexRawQuotient.Value)*L=L := by grind only
      have hs := congrArg (ComplexRawQuotient.scaleRat (-24)) hm
      rw [hs, ←ComplexRawQuotient.neg_scaleRat]
      rfl)

/-- The actual weight-two derivative is the scaled Lambert derivative. -/
theorem tauWeightTwoNomeMap_derivative (q : Scalar) (hq : tauEulerNomeDomain q) :
    (tauWeightTwoNomeMap_holomorphic.derivative q hq).val.Equiv
      (scaleRat (-24) (tauLambertSlopeValue q hq).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (tauWeightTwoNomeMap_holomorphic.derivative q hq).property)
    (hright := scaleRat_valid (tauLambertSlopeValue q hq).property)
  let L := ComplexRawQuotient.ofRaw (tauLambertValue q hq).val (tauLambertValue q hq).property
  let D := ComplexRawQuotient.ofRaw (tauLambertSlopeValue q hq).val (tauLambertSlopeValue q hq).property
  change 0+(0*L+ComplexRawQuotient.scaleRat (-24) 1*D)=ComplexRawQuotient.scaleRat (-24) D
  have hz : (0:ComplexRawQuotient.Value)*L=0 := by grind only
  rw [hz]
  have ha : (0:ComplexRawQuotient.Value)+(0+ComplexRawQuotient.scaleRat (-24) 1*D)=
      ComplexRawQuotient.scaleRat (-24) 1*D := by grind only
  rw [ha, ←ComplexRawQuotient.scaleRat_mul]
  congr 1
  grind only

end ComputableAnalysis.ModularForms
