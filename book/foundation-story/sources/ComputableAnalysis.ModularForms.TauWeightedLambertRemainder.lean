import ComputableAnalysis.ModularForms.TauLambertQuadraticComposition

/-! Exact weighting of actual Lambert first-order remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauWeightedLambertMap_remainder (k N : Nat) (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z) :
    (SeriesLimitLaws.remainder ((tauWeightedLambertMap k N).eval z hz).val
      ((tauWeightedLambertMap k N).eval a ha).val
      ((tauWeightedLambertMap_holomorphic k N).derivative a ha).val (sub z.val a.val)).Equiv
      (scaleRat (((N+1:Nat):Rat)^k)
        (SeriesLimitLaws.remainder ((tauLambertPowerMap N).eval z hz).val
          ((tauLambertPowerMap N).eval a ha).val
          ((tauLambertPowerMap_holomorphic N).derivative a ha).val (sub z.val a.val))) := by
  let F := (tauLambertPowerMap N).eval z hz
  let G := (tauLambertPowerMap N).eval a ha
  let D := (tauLambertPowerMap_holomorphic N).derivative a ha
  let W := (tauWeightedLambertMap_holomorphic k N).derivative a ha
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := W.property)
    (hright := scaleRat_valid D.property) (tauWeightedLambertMap_derivative k N a ha)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := SeriesLimitLaws.remainder_valid _ _ _ _
      ((tauWeightedLambertMap k N).eval z hz).property ((tauWeightedLambertMap k N).eval a ha).property
      W.property (sub_valid z.property a.property))
    (hright := scaleRat_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property
      (sub_valid z.property a.property)))
  let f := ComplexRawQuotient.ofRaw F.val F.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let w := ComplexRawQuotient.ofRaw W.val W.property
  let h := ComplexRawQuotient.ofRaw (sub z.val a.val) (sub_valid z.property a.property)
  change w=ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) d at hw
  change (ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) f-
    ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) g)-w*h=
    ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) ((f-g)-d*h)
  rw [hw, ←ComplexRawQuotient.scaleRat_mul]
  change (ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) f+
    -ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) g)+
    -ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) (d*h)=
    ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^k) ((f+(-g))+(-(d*h)))
  rw [ComplexRawQuotient.scaleRat_add, ComplexRawQuotient.scaleRat_add,
    ComplexRawQuotient.neg_eq_scaleRat_neg_one g, ComplexRawQuotient.neg_eq_scaleRat_neg_one (d*h),
    ComplexRawQuotient.scaleRat_scaleRat, ComplexRawQuotient.scaleRat_scaleRat,
    ComplexRawQuotient.neg_scaleRat, ComplexRawQuotient.neg_scaleRat]
  have hc : (((N+1:Nat):Rat)^k)*(-1) = -(((N+1:Nat):Rat)^k) := by grind only
  rw [hc]

/-- Quadratic control of higher actual degree-one weighted term remainders. -/
theorem tauWeightedLambertOne_actual_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (SeriesLimitLaws.remainder ((tauWeightedLambertMap 1 (N+1)).eval z hz).val
      ((tauWeightedLambertMap 1 (N+1)).eval a ha).val
      ((tauWeightedLambertMap_holomorphic 1 (N+1)).derivative a ha).val (sub z.val a.val))
      (((N+2:Nat):Rat)*(1024*(2*((N+2:Nat):Rat)*(2*(1/1024:Rat))^(N+1)*H)^2+
        64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*(1/1024:Rat))^N*H^2))) := by
  have h := LocalODE.small_scale (Rat.natCast_nonneg : 0≤((N+2:Nat):Rat))
    (tauLambertPower_actual_remainder_bound a z ha hz H hH hd N)
  have he := tauWeightedLambertMap_remainder 1 (N+1) a z ha hz
  simp only [Rat.pow_one] at he
  exact Small.congr
    (scaleRat_valid (SeriesLimitLaws.remainder_valid _ _ _ _
      ((tauLambertPowerMap (N+1)).eval z hz).property ((tauLambertPowerMap (N+1)).eval a ha).property
      ((tauLambertPowerMap_holomorphic (N+1)).derivative a ha).property (sub_valid z.property a.property)))
    (SeriesLimitLaws.remainder_valid _ _ _ _ ((tauWeightedLambertMap 1 (N+1)).eval z hz).property
      ((tauWeightedLambertMap 1 (N+1)).eval a ha).property
      ((tauWeightedLambertMap_holomorphic 1 (N+1)).derivative a ha).property (sub_valid z.property a.property))
    (equiv_symm he) h

end ComputableAnalysis.ModularForms
