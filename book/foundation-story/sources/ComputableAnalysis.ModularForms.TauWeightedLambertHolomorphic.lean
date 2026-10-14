import ComputableAnalysis.ModularForms.TauLambertPowerHolomorphic
import ComputableAnalysis.ModularForms.LambertWeightBound

/-! Actual weighted Lambert terms are holomorphic on the nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauWeightedLambertMap (k N : Nat) : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval q hq := ⟨weightedLambertTerm q (1/1024) k N,
    weightedLambertTerm_valid q _ k (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) N⟩
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr q w hq hw he := scaleRat_equiv ((tauLambertPowerMap N).eval_congr q w hq hw he)

/-- Holomorphicity concerns the literal independently computed term value. -/
def tauWeightedLambertMap_holomorphic (k N : Nat) : Holomorphic (tauWeightedLambertMap k N) := by
  let c : Scalar := ⟨scaleRat (((N+1:Nat):Rat)^k) one, scaleRat_valid (ofQComplex_valid _)⟩
  let hc := constantOn_holomorphic tauEulerNomeDomain_openData c
  let hf := tauLambertPowerMap_holomorphic N
  exact (hc.productOn hf (fun _ h => h)).transfer (tauWeightedLambertMap k N)
    (fun _ h => h) ⟨tauEulerNomeDomain_openData.radius,tauEulerNomeDomain_openData.inside⟩
    (fun q hq => by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((productOn (constantOn tauEulerNomeDomain tauEulerNomeDomain_openData.invariant c)
          (tauLambertPowerMap N) (fun _ h => h)).eval q hq).property)
        (hright := ((tauWeightedLambertMap k N).eval q hq).property)
      let L := ComplexRawQuotient.ofRaw ((tauLambertPowerMap N).eval q hq).val
        ((tauLambertPowerMap N).eval q hq).property
      change ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) 1 * L =
        ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) L
      rw [← ComplexRawQuotient.scaleRat_mul]
      congr 1
      grind only)

/-- Exact scaling rule for the actual weighted term derivative. -/
theorem tauWeightedLambertMap_derivative (k N : Nat) (q : Scalar) (hq : tauEulerNomeDomain q) :
    ((tauWeightedLambertMap_holomorphic k N).derivative q hq).val.Equiv
      (scaleRat (((N+1:Nat):Rat)^k) ((tauLambertPowerMap_holomorphic N).derivative q hq).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((tauWeightedLambertMap_holomorphic k N).derivative q hq).property)
    (hright := scaleRat_valid ((tauLambertPowerMap_holomorphic N).derivative q hq).property)
  let L := ComplexRawQuotient.ofRaw ((tauLambertPowerMap N).eval q hq).val
    ((tauLambertPowerMap N).eval q hq).property
  let D := ComplexRawQuotient.ofRaw ((tauLambertPowerMap_holomorphic N).derivative q hq).val
    ((tauLambertPowerMap_holomorphic N).derivative q hq).property
  change 0*L + ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) 1 * D =
    ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) D
  have hm : (0:ComplexRawQuotient.Value)*L=0 := by grind only
  rw [hm]
  have ha : (0:ComplexRawQuotient.Value)+ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) 1 * D =
      ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) 1 * D := by grind only
  rw [ha, ← ComplexRawQuotient.scaleRat_mul]
  congr 1
  grind only

end ComputableAnalysis.ModularForms
