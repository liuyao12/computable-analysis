import ComputableAnalysis.ModularForms.TauLambertSlopeAgreement

/-! Actual weighted Lambert term slopes in every degree. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauWeightedLambertSlope_actual (q : Scalar) (hq : tauEulerNomeDomain q) (k N : Nat) :
    ((tauWeightedLambertMap_holomorphic k N).derivative q hq).val.Equiv
      (scaleRat (((N+1:Nat):Rat)^(k+1)) (mul (LocalODE.power q.val N)
        (lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius (1/1024) N)
          (nomePowerRadius_nonneg _ (by decide +kernel) N)
          (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
          (nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) N)).val)) := by
  let W := (tauWeightedLambertMap_holomorphic k N).derivative q hq
  let L := (tauLambertPowerMap_holomorphic N).derivative q hq
  let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial
  let D := lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius (1/1024) N)
    (nomePowerRadius_nonneg _ (by decide +kernel) N)
    (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
    (nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) N)
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := W.property)
    (hright := scaleRat_valid L.property) (tauWeightedLambertMap_derivative k N q hq)
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := L.property)
    (hright := mul_valid D.property M.property) (tauLambertPowerMap_derivative N q hq)
  have hm := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := M.property)
    (hright := scaleRat_valid (LocalODE.power_valid _ q.property N)) (tauCoordinatePower_derivative q N)
  let w := ComplexRawQuotient.ofRaw W.val W.property
  let l := ComplexRawQuotient.ofRaw L.val L.property
  let m := ComplexRawQuotient.ofRaw M.val M.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let p := ComplexRawQuotient.ofRaw (LocalODE.power q.val N) (LocalODE.power_valid _ q.property N)
  change w=ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) l at hw
  change l=d*m at hl
  change m=ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) p at hm
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := W.property)
    (hright := scaleRat_valid (mul_valid (LocalODE.power_valid _ q.property N) D.property))
  change w=ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^(k+1)) (p*d)
  rw [hw,hl,hm,ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.scaleRat_scaleRat]
  have hc : (((N+1:Nat):Rat)^k)*((N+1:Nat):Rat)=((N+1:Nat):Rat)^(k+1) := by
    rw [Rat.pow_succ]
  rw [hc]
  congr 1
  grind only

end ComputableAnalysis.ModularForms
