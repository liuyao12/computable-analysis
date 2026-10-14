import ComputableAnalysis.ModularForms.TauHigherLambertHolomorphic
import ComputableAnalysis.ModularForms.LatticeInvariantsNormalizedFourier

/-! Actual holomorphic normalized Eisenstein nome maps of weights four and six. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private def normalizedMap (k : Nat) (hk : k≤5) (c : Rat) : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval := fun q hq => ⟨add one (scaleRat c (tauHigherLambertValue q hq k hk).val),
    add_valid (ofQComplex_valid _) (scaleRat_valid (tauHigherLambertValue q hq k hk).property)⟩
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr := fun q w hq hw he => add_equiv (equiv_refl one (ofQComplex_valid _))
    (scaleRat_equiv (tauHigherLambertValue_congr k hk q w hq hw he))

private noncomputable def normalizedHolomorphic (k : Nat) (hk : k≤5) (c : Rat) :
    Holomorphic (normalizedMap k hk c) := by
  let C : Scalar := ⟨scaleRat c one,scaleRat_valid (ofQComplex_valid _)⟩
  let hc := constantOn_holomorphic tauEulerNomeDomain_openData C
  let ho := constantOn_holomorphic tauEulerNomeDomain_openData oneScalar
  let hp := hc.productOn (tauHigherLambertNomeMap_holomorphic k hk) (fun _ h => h)
  exact (ho.sumOn hp (fun _ h => h)).transfer (normalizedMap k hk c) (fun _ h => h)
    ⟨tauEulerNomeDomain_openData.radius,tauEulerNomeDomain_openData.inside⟩
    (fun q hq => by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((sumOn (constantOn tauEulerNomeDomain tauEulerNomeDomain_openData.invariant oneScalar)
          (productOn (constantOn tauEulerNomeDomain tauEulerNomeDomain_openData.invariant C)
            (tauHigherLambertNomeMap k hk) (fun _ h => h)) (fun _ h => h)).eval q hq).property)
        (hright := ((normalizedMap k hk c).eval q hq).property)
      let L := ComplexRawQuotient.ofRaw (tauHigherLambertValue q hq k hk).val (tauHigherLambertValue q hq k hk).property
      change 1+ComplexRawQuotient.scaleRat c 1*L=1+ComplexRawQuotient.scaleRat c L
      rw [←ComplexRawQuotient.scaleRat_mul]
      congr 1
      congr 1
      grind only)

private theorem normalizedDerivative (k : Nat) (hk : k≤5) (c : Rat) (q : Scalar) (hq : tauEulerNomeDomain q) :
    ((normalizedHolomorphic k hk c).derivative q hq).val.Equiv
      (scaleRat c (tauWeightedLambertSlopeValue q hq k hk).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((normalizedHolomorphic k hk c).derivative q hq).property)
    (hright := scaleRat_valid (tauWeightedLambertSlopeValue q hq k hk).property)
  let L := ComplexRawQuotient.ofRaw (tauHigherLambertValue q hq k hk).val (tauHigherLambertValue q hq k hk).property
  let D := ComplexRawQuotient.ofRaw (tauWeightedLambertSlopeValue q hq k hk).val (tauWeightedLambertSlopeValue q hq k hk).property
  change 0+(0*L+ComplexRawQuotient.scaleRat c 1*D)=ComplexRawQuotient.scaleRat c D
  have hz : (0:ComplexRawQuotient.Value)*L=0 := by grind only
  rw [hz]
  have ha : (0:ComplexRawQuotient.Value)+(0+ComplexRawQuotient.scaleRat c 1*D)=ComplexRawQuotient.scaleRat c 1*D := by grind only
  rw [ha,←ComplexRawQuotient.scaleRat_mul]
  congr 1
  grind only

def nomeEisensteinFourMap : DomainFunctions.Map := normalizedMap 3 (by omega) 240
def nomeEisensteinSixMap : DomainFunctions.Map := normalizedMap 5 (by omega) (-504)

noncomputable def nomeEisensteinFourMap_holomorphic : Holomorphic nomeEisensteinFourMap :=
  normalizedHolomorphic 3 (by omega) 240
noncomputable def nomeEisensteinSixMap_holomorphic : Holomorphic nomeEisensteinSixMap :=
  normalizedHolomorphic 5 (by omega) (-504)

theorem nomeEisensteinFourMap_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (nomeEisensteinFourMap.eval q hq).val.Equiv
      (nomeEisensteinFour q (1/1024) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq)).val :=
  equiv_refl _ (nomeEisensteinFourMap.eval q hq).property

theorem nomeEisensteinSixMap_agreement (q : Scalar) (hq : tauEulerNomeDomain q) :
    (nomeEisensteinSixMap.eval q hq).val.Equiv
      (nomeEisensteinSix q (1/1024) (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq)).val :=
  equiv_refl _ (nomeEisensteinSixMap.eval q hq).property

theorem nomeEisensteinFourMap_derivative (q : Scalar) (hq : tauEulerNomeDomain q) :
    (nomeEisensteinFourMap_holomorphic.derivative q hq).val.Equiv
      (scaleRat 240 (tauWeightedLambertSlopeValue q hq 3 (by omega)).val) :=
  normalizedDerivative 3 (by omega) 240 q hq

theorem nomeEisensteinSixMap_derivative (q : Scalar) (hq : tauEulerNomeDomain q) :
    (nomeEisensteinSixMap_holomorphic.derivative q hq).val.Equiv
      (scaleRat (-504) (tauWeightedLambertSlopeValue q hq 5 (by omega)).val) :=
  normalizedDerivative 5 (by omega) (-504) q hq

end ComputableAnalysis.ModularForms
