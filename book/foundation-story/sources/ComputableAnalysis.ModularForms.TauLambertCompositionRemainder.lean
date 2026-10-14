import ComputableAnalysis.ModularForms.TauLambertDerivativeMaps

/-! Exact decomposition of the actual Lambert monomial remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Separate the outer Lambert error from the actual monomial error. -/
theorem tauLambertPower_remainder_decomposition (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z) (N : Nat) :
    let A := nomePowerScalar a N
    let Z := nomePowerScalar z N
    let D := lambertDiskDerivative A (nomePowerRadius (1/1024) N)
      (nomePowerRadius_nonneg _ (by decide +kernel) N)
      (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
      (nomePowerScalar_small a _ (by decide +kernel) (LocalODE.interior_bound _ a ha) N)
    let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative a trivial
    (SeriesLimitLaws.remainder ((tauLambertPowerMap N).eval z hz).val
      ((tauLambertPowerMap N).eval a ha).val (mul D.val M.val) (sub z.val a.val)).Equiv
      (add (SeriesLimitLaws.remainder ((tauLambertPowerMap N).eval z hz).val
        ((tauLambertPowerMap N).eval a ha).val D.val (sub Z.val A.val))
        (mul D.val (SeriesLimitLaws.remainder Z.val A.val M.val (sub z.val a.val)))) := by
  intro A Z D M
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := SeriesLimitLaws.remainder_valid _ _ _ _
      ((tauLambertPowerMap N).eval z hz).property ((tauLambertPowerMap N).eval a ha).property
      (mul_valid D.property M.property) (sub_valid z.property a.property))
    (hright := add_valid
      (SeriesLimitLaws.remainder_valid _ _ _ _ ((tauLambertPowerMap N).eval z hz).property
        ((tauLambertPowerMap N).eval a ha).property D.property (sub_valid Z.property A.property))
      (mul_valid D.property (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property
        (sub_valid z.property a.property))))
  let F := ComplexRawQuotient.ofRaw ((tauLambertPowerMap N).eval z hz).val ((tauLambertPowerMap N).eval z hz).property
  let G := ComplexRawQuotient.ofRaw ((tauLambertPowerMap N).eval a ha).val ((tauLambertPowerMap N).eval a ha).property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let m := ComplexRawQuotient.ofRaw M.val M.property
  let X := ComplexRawQuotient.ofRaw (sub Z.val A.val) (sub_valid Z.property A.property)
  let h := ComplexRawQuotient.ofRaw (sub z.val a.val) (sub_valid z.property a.property)
  change (F-G)-(d*m)*h=((F-G)-d*X)+d*(X-m*h)
  grind only

/-- Uniform control of the multiplier of the inner monomial remainder. -/
theorem tauLambertPower_outer_derivative_bound (a : Scalar) (ha : tauEulerNomeDomain a) (N : Nat) :
    Small (lambertDiskDerivative (nomePowerScalar a N) (nomePowerRadius (1/1024) N)
      (nomePowerRadius_nonneg _ (by decide +kernel) N)
      (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
      (nomePowerScalar_small a _ (by decide +kernel) (LocalODE.interior_bound _ a ha) N)).val 32 :=
  lambertDiskDerivative_bound _ _ _ _ _

end ComputableAnalysis.ModularForms
