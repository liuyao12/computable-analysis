import ComputableAnalysis.ModularForms.TauWeightedLambertRemainder
import ComputableAnalysis.ModularForms.TauLambertFirstRemainder

namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Quadratic control of higher actual degree-one weighted term remainders. -/
theorem tauWeightedLambertOne_first_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder ((tauWeightedLambertMap 1 0).eval z hz).val
      ((tauWeightedLambertMap 1 0).eval a ha).val
      ((tauWeightedLambertMap_holomorphic 1 0).derivative a ha).val (sub z.val a.val))
      (4096*H^2) := by
  have h := LocalODE.small_scale (Rat.natCast_nonneg : (0:Rat)≤1)
    (tauLambertPower_first_actual_remainder_bound a z ha hz H hH hd)
  have he := tauWeightedLambertMap_remainder 1 0 a z ha hz
  simp only [Rat.pow_one] at he
  have hh := Small.congr
    (scaleRat_valid (SeriesLimitLaws.remainder_valid _ _ _ _
      ((tauLambertPowerMap 0).eval z hz).property ((tauLambertPowerMap 0).eval a ha).property
      ((tauLambertPowerMap_holomorphic 0).derivative a ha).property (sub_valid z.property a.property)))
    (SeriesLimitLaws.remainder_valid _ _ _ _ ((tauWeightedLambertMap 1 0).eval z hz).property
      ((tauWeightedLambertMap 1 0).eval a ha).property
      ((tauWeightedLambertMap_holomorphic 1 0).derivative a ha).property (sub_valid z.property a.property))
    (equiv_symm he) h
  simpa only [show ((1:Nat):Rat)=1 by rfl, Rat.one_mul] using hh

end ComputableAnalysis.ModularForms
