import ComputableAnalysis.ModularForms.TauLambertInnerRemainder

/-! Combined quadratic remainders for actual Lambert monomial compositions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauLambertPower_combined_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    let D := lambertDiskDerivative (nomePowerScalar a (N+1)) (nomePowerRadius (1/1024) (N+1))
      (nomePowerRadius_nonneg _ (by decide +kernel) (N+1))
      (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) (N+1))
      (nomePowerScalar_small a _ (by decide +kernel) (LocalODE.interior_bound _ a ha) (N+1))
    let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+2)).derivative a trivial
    Small (SeriesLimitLaws.remainder ((tauLambertPowerMap (N+1)).eval z hz).val
      ((tauLambertPowerMap (N+1)).eval a ha).val (mul D.val M.val) (sub z.val a.val))
      (1024*(2*((N+2:Nat):Rat)*(2*(1/1024:Rat))^(N+1)*H)^2+
        64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2)) := by
  intro D M
  let A := nomePowerScalar a (N+1)
  let Z := nomePowerScalar z (N+1)
  let F := (tauLambertPowerMap (N+1)).eval z hz
  let G := (tauLambertPowerMap (N+1)).eval a ha
  have ho := tauLambertPower_outer_remainder_bound a z (1/1024) H
    (by decide +kernel) (by decide +kernel) hH (LocalODE.interior_bound _ a ha)
    (LocalODE.interior_bound _ z hz) hd (N+1)
  have he : (sub (sub F.val G.val) (mul (sub Z.val A.val) D.val)).Equiv
      (SeriesLimitLaws.remainder F.val G.val D.val (sub Z.val A.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid F.property G.property) (mul_valid (sub_valid Z.property A.property) D.property))
      (hright := SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property (sub_valid Z.property A.property))
    let f := ComplexRawQuotient.ofRaw F.val F.property
    let g := ComplexRawQuotient.ofRaw G.val G.property
    let d := ComplexRawQuotient.ofRaw D.val D.property
    let x := ComplexRawQuotient.ofRaw (sub Z.val A.val) (sub_valid Z.property A.property)
    change (f-g)-x*d=(f-g)-d*x
    grind only
  have hob := Small.congr
    (sub_valid (sub_valid F.property G.property) (mul_valid (sub_valid Z.property A.property) D.property))
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property (sub_valid Z.property A.property)) he ho
  have hi := tauCoordinatePower_actual_remainder_bound a z (1/1024) H (by decide +kernel) hH
    (LocalODE.interior_bound _ a ha) (LocalODE.interior_bound _ z hz) hd N
  have hb : 0≤2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2 :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg)
      Rat.natCast_nonneg) (Rat.pow_nonneg (by decide +kernel))) (Rat.pow_nonneg hH)
  have hm := Small.mul D.property
    (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property (sub_valid z.property a.property))
    (by decide +kernel : (0:Rat)≤32) hb (tauLambertPower_outer_derivative_bound a ha (N+1)) hi
  have hs := LocalODE.small_add hob hm
  have hc := tauLambertPower_remainder_decomposition a z ha hz (N+1)
  have hh := Small.congr
    (add_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property (sub_valid Z.property A.property))
      (mul_valid D.property (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property (sub_valid z.property a.property))))
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property (mul_valid D.property M.property) (sub_valid z.property a.property))
    (equiv_symm hc) hs
  exact hh.mono (by grind only)

/-- The combined bound applies to the actual holomorphic derivative. -/
theorem tauLambertPower_actual_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (SeriesLimitLaws.remainder ((tauLambertPowerMap (N+1)).eval z hz).val
      ((tauLambertPowerMap (N+1)).eval a ha).val
      ((tauLambertPowerMap_holomorphic (N+1)).derivative a ha).val (sub z.val a.val))
      (1024*(2*((N+2:Nat):Rat)*(2*(1/1024:Rat))^(N+1)*H)^2+
        64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2)) := by
  let F := (tauLambertPowerMap (N+1)).eval z hz
  let G := (tauLambertPowerMap (N+1)).eval a ha
  let D := lambertDiskDerivative (nomePowerScalar a (N+1)) (nomePowerRadius (1/1024) (N+1))
    (nomePowerRadius_nonneg _ (by decide +kernel) (N+1))
    (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) (N+1))
    (nomePowerScalar_small a _ (by decide +kernel) (LocalODE.interior_bound _ a ha) (N+1))
  let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+2)).derivative a trivial
  let L := (tauLambertPowerMap_holomorphic (N+1)).derivative a ha
  have he := FunctionTheory.sub_congr (equiv_refl (sub F.val G.val) (sub_valid F.property G.property))
    (mul_equiv (mul_valid D.property M.property) L.property
      (sub_valid z.property a.property) (sub_valid z.property a.property)
      (equiv_symm (tauLambertPowerMap_derivative (N+1) a ha))
      (equiv_refl _ (sub_valid z.property a.property)))
  exact Small.congr
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property (mul_valid D.property M.property) (sub_valid z.property a.property))
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property L.property (sub_valid z.property a.property))
    he (tauLambertPower_combined_remainder_bound a z ha hz H hH hd N)

end ComputableAnalysis.ModularForms
