import ComputableAnalysis.ModularForms.TauWeightedLambertHolomorphic
import ComputableAnalysis.ModularForms.TauLambertSlopeBounds

/-! Agreement of actual weighted term derivatives with executable slopes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem weightedLambertOneSlope_actual (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    ((tauWeightedLambertMap_holomorphic 1 N).derivative q hq).val.Equiv
      (weightedLambertOneSlope q (1/1024) (by decide +kernel) (by decide +kernel)
        (LocalODE.interior_bound _ q hq) N).val := by
  let W := (tauWeightedLambertMap_holomorphic 1 N).derivative q hq
  let L := (tauLambertPowerMap_holomorphic N).derivative q hq
  let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial
  let D := lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius (1/1024) N)
    (nomePowerRadius_nonneg _ (by decide +kernel) N)
    (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
    (nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) N)
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := W.property)
    (hright := scaleRat_valid L.property) (tauWeightedLambertMap_derivative 1 N q hq)
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := L.property)
    (hright := mul_valid D.property M.property) (tauLambertPowerMap_derivative N q hq)
  have hm := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := M.property)
    (hright := scaleRat_valid (LocalODE.power_valid _ q.property N)) (tauCoordinatePower_derivative q N)
  let w := ComplexRawQuotient.ofRaw W.val W.property
  let l := ComplexRawQuotient.ofRaw L.val L.property
  let m := ComplexRawQuotient.ofRaw M.val M.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let p := ComplexRawQuotient.ofRaw (LocalODE.power q.val N) (LocalODE.power_valid _ q.property N)
  change w=ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^1) l at hw
  change l=d*m at hl
  change m=ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) p at hm
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := W.property)
    (hright := (weightedLambertOneSlope q (1/1024) (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) N).property)
  change w=ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^2) (p*d)
  rw [hw, hl, hm, Rat.pow_one, ComplexRawQuotient.mul_scaleRat,
    ComplexRawQuotient.scaleRat_scaleRat]
  have hc : ((N+1:Nat):Rat)*((N+1:Nat):Rat)=((N+1:Nat):Rat)^2 := by
    rw [Rat.pow_succ, Rat.pow_one]
  rw [hc]
  congr 1
  grind only

/-- Actual term derivatives have the summable slope majorant. -/
theorem weightedLambertOne_actual_derivative_bound (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    Small ((tauWeightedLambertMap_holomorphic 1 N).derivative q hq).val (64*(1/128:Rat)^N) := by
  have h := weightedLambertOneSlope_geometric_bound q (1/1024)
    (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq) N
  have hh := Small.congr
    (weightedLambertOneSlope q (1/1024) (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) N).property
    ((tauWeightedLambertMap_holomorphic 1 N).derivative q hq).property
    (equiv_symm (weightedLambertOneSlope_actual q hq N)) h
  simpa only [show (8:Rat)*(1/1024)=1/128 by decide +kernel] using hh

end ComputableAnalysis.ModularForms
