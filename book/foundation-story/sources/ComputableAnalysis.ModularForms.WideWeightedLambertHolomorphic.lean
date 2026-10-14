import ComputableAnalysis.ModularForms.WideLambertFifthDerivative
import ComputableAnalysis.ModularForms.WideLambertPowerHolomorphic
import ComputableAnalysis.ModularForms.LambertWeightBound

/-! Actual weighted Lambert terms are holomorphic on the nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def wideWeightedLambertMap (k N : Nat) : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q hq := ⟨weightedLambertTerm q (1/64) k N,
    weightedLambertTerm_valid q _ k (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) N⟩
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w hq hw he := scaleRat_equiv ((wideLambertPowerMap N).eval_congr q w hq hw he)

/-- Holomorphicity concerns the literal independently computed term value. -/
def wideWeightedLambertMap_holomorphic (k N : Nat) : Holomorphic (wideWeightedLambertMap k N) := by
  let c : Scalar := ⟨scaleRat (((N+1:Nat):Rat)^k) one, scaleRat_valid (ofQComplex_valid _)⟩
  let hc := constantOn_holomorphic wideLambertFifthDomain_openData c
  let hf := wideLambertPowerMap_holomorphic N
  exact (hc.productOn hf (fun _ h => h)).transfer (wideWeightedLambertMap k N)
    (fun _ h => h) ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
    (fun q hq => by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ((productOn (constantOn wideLambertFifthDomain wideLambertFifthDomain_openData.invariant c)
          (wideLambertPowerMap N) (fun _ h => h)).eval q hq).property)
        (hright := ((wideWeightedLambertMap k N).eval q hq).property)
      let L := ComplexRawQuotient.ofRaw ((wideLambertPowerMap N).eval q hq).val
        ((wideLambertPowerMap N).eval q hq).property
      change ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) 1 * L =
        ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) L
      rw [← ComplexRawQuotient.scaleRat_mul]
      congr 1
      grind only)

/-- Exact scaling rule for the actual weighted term derivative. -/
theorem wideWeightedLambertMap_derivative (k N : Nat) (q : Scalar) (hq : wideLambertFifthDomain q) :
    ((wideWeightedLambertMap_holomorphic k N).derivative q hq).val.Equiv
      (scaleRat (((N+1:Nat):Rat)^k) ((wideLambertPowerMap_holomorphic N).derivative q hq).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((wideWeightedLambertMap_holomorphic k N).derivative q hq).property)
    (hright := scaleRat_valid ((wideLambertPowerMap_holomorphic N).derivative q hq).property)
  let L := ComplexRawQuotient.ofRaw ((wideLambertPowerMap N).eval q hq).val
    ((wideLambertPowerMap N).eval q hq).property
  let D := ComplexRawQuotient.ofRaw ((wideLambertPowerMap_holomorphic N).derivative q hq).val
    ((wideLambertPowerMap_holomorphic N).derivative q hq).property
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
