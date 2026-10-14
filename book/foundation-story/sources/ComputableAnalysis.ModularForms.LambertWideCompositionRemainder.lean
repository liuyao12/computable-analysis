import ComputableAnalysis.ModularForms.TauLambertInnerRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Exact decomposition of a composed first-order error for supplied represented values. -/
theorem scalar_composition_remainder (F G A Z D M h : Scalar) :
    (SeriesLimitLaws.remainder F.val G.val (mul D.val M.val) h.val).Equiv
      (add (SeriesLimitLaws.remainder F.val G.val D.val (sub Z.val A.val))
        (mul D.val (SeriesLimitLaws.remainder Z.val A.val M.val h.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property
      (mul_valid D.property M.property) h.property)
    (hright := add_valid
      (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property (sub_valid Z.property A.property))
      (mul_valid D.property (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property h.property)))
  let f := ComplexRawQuotient.ofRaw F.val F.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  let a := ComplexRawQuotient.ofRaw A.val A.property
  let z := ComplexRawQuotient.ofRaw Z.val Z.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let m := ComplexRawQuotient.ofRaw M.val M.property
  let v := ComplexRawQuotient.ofRaw h.val h.property
  change (f-g)-(d*m)*v=((f-g)-d*(z-a))+d*((z-a)-m*v)
  grind only

/-- Actual Lambert monomial remainder control on an arbitrary justified rational disk. -/
theorem nomeLambertPower_wide_composition_remainder (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hl : 4*R≤(1:Rat)/2) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hd : Small (sub z.val a.val) H) (N : Nat) :
    let D := lambertDiskDerivative (nomePowerScalar a (N+1)) (nomePowerRadius R (N+1))
      (nomePowerRadius_nonneg R hR (N+1)) (nomePowerRadius_local R hR hl (N+1))
      (nomePowerScalar_small a R hR ha (N+1))
    let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+2)).derivative a trivial
    Small (SeriesLimitLaws.remainder (nomeLambertPower z R (N+1)) (nomeLambertPower a R (N+1))
      (mul D.val M.val) (sub z.val a.val))
      (1024*(2*((N+2:Nat):Rat)*(2*R)^(N+1)*H)^2+
        64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2)) := by
  intro D M
  let A := nomePowerScalar a (N+1)
  let Z := nomePowerScalar z (N+1)
  let F : Scalar := ⟨nomeLambertPower z R (N+1),nomeLambertPower_valid z R hR hl hz (N+1)⟩
  let G : Scalar := ⟨nomeLambertPower a R (N+1),nomeLambertPower_valid a R hR hl ha (N+1)⟩
  let v : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  have ho := tauLambertPower_outer_remainder_bound a z R H hR hl hH ha hz hd (N+1)
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
  have hi := tauCoordinatePower_actual_remainder_bound a z R H hR hH ha hz hd N
  have hb : 0≤2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2 :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) Rat.natCast_nonneg)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hR))) (Rat.pow_nonneg hH)
  have hm := Small.mul D.property
    (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property v.property)
    (show (0:Rat)≤32 by decide +kernel) hb
    (lambertDiskDerivative_bound _ _ _ _ _) hi
  have hs := LocalODE.small_add hob hm
  have hec := scalar_composition_remainder F G A Z D M v
  have hbound := Small.congr
    (add_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property (sub_valid Z.property A.property))
      (mul_valid D.property (SeriesLimitLaws.remainder_valid _ _ _ _ Z.property A.property M.property v.property)))
    (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property (mul_valid D.property M.property) v.property)
    (equiv_symm hec) hs
  have hc : (2:Rat)*32*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2)=
      64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2) := by grind only
  rw [hc] at hbound
  exact hbound
end ComputableAnalysis.ModularForms
