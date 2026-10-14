import ComputableAnalysis.ModularForms.TauWeightedLambertFirstRemainder

/-! Actual quadratic remainder bounds for weighted Lambert terms in every degree. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Quadratic control of higher actual degree-one weighted term remainders. -/
theorem tauWeightedLambert_actual_remainder_bound (k : Nat) (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (SeriesLimitLaws.remainder ((tauWeightedLambertMap k (N+1)).eval z hz).val
      ((tauWeightedLambertMap k (N+1)).eval a ha).val
      ((tauWeightedLambertMap_holomorphic k (N+1)).derivative a ha).val (sub z.val a.val))
      ((((N+2:Nat):Rat)^k)*(1024*(2*((N+2:Nat):Rat)*(2*(1/1024:Rat))^(N+1)*H)^2+
        64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2))) := by
  have h := LocalODE.small_scale (Rat.pow_nonneg (n := k) (Rat.natCast_nonneg : 0≤((N+2:Nat):Rat)))
    (tauLambertPower_actual_remainder_bound a z ha hz H hH hd N)
  have he := tauWeightedLambertMap_remainder k (N+1) a z ha hz
  exact Small.congr
    (scaleRat_valid (SeriesLimitLaws.remainder_valid _ _ _ _
      ((tauLambertPowerMap (N+1)).eval z hz).property ((tauLambertPowerMap (N+1)).eval a ha).property
      ((tauLambertPowerMap_holomorphic (N+1)).derivative a ha).property (sub_valid z.property a.property)))
    (SeriesLimitLaws.remainder_valid _ _ _ _ ((tauWeightedLambertMap k (N+1)).eval z hz).property
      ((tauWeightedLambertMap k (N+1)).eval a ha).property
      ((tauWeightedLambertMap_holomorphic k (N+1)).derivative a ha).property (sub_valid z.property a.property))
    (equiv_symm he) h

/-- Quadratic control of higher actual degree-one weighted term remainders. -/
theorem tauWeightedLambert_first_remainder_bound (k : Nat) (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder ((tauWeightedLambertMap k 0).eval z hz).val
      ((tauWeightedLambertMap k 0).eval a ha).val
      ((tauWeightedLambertMap_holomorphic k 0).derivative a ha).val (sub z.val a.val))
      (4096*H^2) := by
  have h := LocalODE.small_scale (Rat.pow_nonneg (n := k) (Rat.natCast_nonneg : (0:Rat)≤1))
    (tauLambertPower_first_actual_remainder_bound a z ha hz H hH hd)
  have he := tauWeightedLambertMap_remainder k 0 a z ha hz
  have hh := Small.congr
    (scaleRat_valid (SeriesLimitLaws.remainder_valid _ _ _ _
      ((tauLambertPowerMap 0).eval z hz).property ((tauLambertPowerMap 0).eval a ha).property
      ((tauLambertPowerMap_holomorphic 0).derivative a ha).property (sub_valid z.property a.property)))
    (SeriesLimitLaws.remainder_valid _ _ _ _ ((tauWeightedLambertMap k 0).eval z hz).property
      ((tauWeightedLambertMap k 0).eval a ha).property
      ((tauWeightedLambertMap_holomorphic k 0).derivative a ha).property (sub_valid z.property a.property))
    (equiv_symm he) h
  have hp (n : Nat) : (1:Rat)^n=1 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Rat.pow_succ,ih]; exact Rat.one_mul 1
  simpa only [show ((1:Nat):Rat)=1 by rfl, hp k, Rat.one_mul] using hh

end ComputableAnalysis.ModularForms
