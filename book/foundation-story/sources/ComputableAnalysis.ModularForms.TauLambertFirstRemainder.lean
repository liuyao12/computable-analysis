import ComputableAnalysis.ModularForms.TauLambertQuadraticComposition

namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauLambertPower_first_combined_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    let D := lambertDiskDerivative (nomePowerScalar a 0) (nomePowerRadius (1/1024) 0)
      (nomePowerRadius_nonneg _ (by decide +kernel) 0)
      (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) 0)
      (nomePowerScalar_small a _ (by decide +kernel) (LocalODE.interior_bound _ a ha) 0)
    let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic 1).derivative a trivial
    Small (SeriesLimitLaws.remainder ((tauLambertPowerMap 0).eval z hz).val
      ((tauLambertPowerMap 0).eval a ha).val (mul D.val M.val) (sub z.val a.val))
      (4096*H^2) := by
  intro D M
  let A := nomePowerScalar a 0
  let Z := nomePowerScalar z 0
  let F := (tauLambertPowerMap 0).eval z hz
  let G := (tauLambertPowerMap 0).eval a ha
  have ho := tauLambertPower_outer_remainder_bound a z (1/1024) H
    (by decide +kernel) (by decide +kernel) hH (LocalODE.interior_bound _ a ha)
    (LocalODE.interior_bound _ z hz) hd 0
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
  have hi : Small (SeriesLimitLaws.remainder Z.val A.val M.val (sub z.val a.val)) 0 :=
    Small.congr (ofQComplex_valid _)
      (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property (sub_valid z.property a.property))
      (equiv_symm (tauCoordinatePower_first_remainder_zero a z)) (Small.zero Rat.le_refl)
  have hm := Small.mul D.property
    (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property (sub_valid z.property a.property))
    (by decide +kernel : (0:Rat)≤32) (Rat.le_refl : (0:Rat)≤0) (tauLambertPower_outer_derivative_bound a ha 0) hi
  have hs := LocalODE.small_add hob hm
  have hc := tauLambertPower_remainder_decomposition a z ha hz 0
  have hh := Small.congr
    (add_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property (sub_valid Z.property A.property))
      (mul_valid D.property (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property (sub_valid z.property a.property))))
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property (mul_valid D.property M.property) (sub_valid z.property a.property))
    (equiv_symm hc) hs
  apply hh.mono
  simp only [Rat.pow_zero, show ((0+1:Nat):Rat)=1 by rfl, Rat.mul_one, Rat.mul_zero, Rat.add_zero]
  change 1024*(2*H)^2 ≤ 4096*H^2
  simp only [Rat.pow_succ, Rat.pow_one]
  grind only

/-- The combined bound applies to the actual holomorphic derivative. -/
theorem tauLambertPower_first_actual_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder ((tauLambertPowerMap 0).eval z hz).val
      ((tauLambertPowerMap 0).eval a ha).val
      ((tauLambertPowerMap_holomorphic 0).derivative a ha).val (sub z.val a.val))
      (4096*H^2) := by
  let F := (tauLambertPowerMap 0).eval z hz
  let G := (tauLambertPowerMap 0).eval a ha
  let D := lambertDiskDerivative (nomePowerScalar a 0) (nomePowerRadius (1/1024) 0)
    (nomePowerRadius_nonneg _ (by decide +kernel) 0)
    (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) 0)
    (nomePowerScalar_small a _ (by decide +kernel) (LocalODE.interior_bound _ a ha) 0)
  let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic 1).derivative a trivial
  let L := (tauLambertPowerMap_holomorphic 0).derivative a ha
  have he := FunctionTheory.sub_congr (equiv_refl (sub F.val G.val) (sub_valid F.property G.property))
    (mul_equiv (mul_valid D.property M.property) L.property
      (sub_valid z.property a.property) (sub_valid z.property a.property)
      (equiv_symm (tauLambertPowerMap_derivative 0 a ha))
      (equiv_refl _ (sub_valid z.property a.property)))
  exact Small.congr
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property (mul_valid D.property M.property) (sub_valid z.property a.property))
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property L.property (sub_valid z.property a.property))
    he (tauLambertPower_first_combined_remainder_bound a z ha hz H hH hd)

end ComputableAnalysis.ModularForms
