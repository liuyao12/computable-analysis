import ComputableAnalysis.ModularForms.LambertWideCompositionRemainder
import ComputableAnalysis.ModularForms.LambertSharperSlopeBound
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Rational weighting preserves the supplied first-order remainder exactly. -/
theorem scalar_scaled_remainder (F G D h : Scalar) (r : Rat) :
    (SeriesLimitLaws.remainder (scaleRat r F.val) (scaleRat r G.val) (scaleRat r D.val) h.val).Equiv
      (scaleRat r (SeriesLimitLaws.remainder F.val G.val D.val h.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := SeriesLimitLaws.remainder_valid _ _ _ _ (scaleRat_valid F.property)
      (scaleRat_valid G.property) (scaleRat_valid D.property) h.property)
    (hright := scaleRat_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property D.property h.property))
  let f := ComplexRawQuotient.ofRaw F.val F.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let v := ComplexRawQuotient.ofRaw h.val h.property
  have lin (x : ComplexRawQuotient.Value) : ComplexRawQuotient.scaleRat r x=ComplexRawQuotient.scaleRat r 1*x := by
    rw [←ComplexRawQuotient.scaleRat_mul]
    congr 1
    grind only
  change (ComplexRawQuotient.scaleRat r f-ComplexRawQuotient.scaleRat r g)-
    ComplexRawQuotient.scaleRat r d*v=ComplexRawQuotient.scaleRat r ((f-g)-d*v)
  rw [lin f,lin g,lin d,lin ((f-g)-d*v)]
  grind only

/-- Exact connection between the literal weighted slope and the composed actual monomial derivative. -/
theorem weightedLambertSlope_wide_composition (a : Scalar) (R : Rat) (k : Nat)
    (hR : 0≤R) (hl : 4*R≤(1:Rat)/2) (ha : Small a.val R) (n : Nat) :
    let D := lambertDiskDerivative (nomePowerScalar a n) (nomePowerRadius R n)
      (nomePowerRadius_nonneg R hR n) (nomePowerRadius_local R hR hl n) (nomePowerScalar_small a R hR ha n)
    let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (n+1)).derivative a trivial
    (weightedLambertSlope a R k hR hl ha n).val.Equiv
      (scaleRat (((n+1:Nat):Rat)^k) (mul D.val M.val)) := by
  intro D M
  have hm := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := M.property)
    (hright := scaleRat_valid (LocalODE.power_valid _ a.property n)) (tauCoordinatePower_derivative a n)
  let m := ComplexRawQuotient.ofRaw M.val M.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let p := ComplexRawQuotient.ofRaw (LocalODE.power a.val n) (LocalODE.power_valid _ a.property n)
  change m=ComplexRawQuotient.scaleRat ((n+1:Nat):Rat) p at hm
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (weightedLambertSlope a R k hR hl ha n).property) (hright := scaleRat_valid (mul_valid D.property M.property))
  change ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^(k+1)) (p*d)=
    ComplexRawQuotient.scaleRat (((n+1:Nat):Rat)^k) (d*m)
  rw [hm,ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.scaleRat_scaleRat,Rat.pow_succ]
  congr 1
  grind only

/-- The literal actual weighted terms and literal slope satisfy the general-disk quadratic bound. -/
theorem weightedLambertTerm_wide_remainder_bound (k : Nat) (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hl : 4*R≤(1:Rat)/2) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (SeriesLimitLaws.remainder (weightedLambertTerm z R k (N+1))
      (weightedLambertTerm a R k (N+1)) (weightedLambertSlope a R k hR hl ha (N+1)).val (sub z.val a.val))
      ((((N+2:Nat):Rat)^k)*(1024*(2*((N+2:Nat):Rat)*(2*R)^(N+1)*H)^2+
        64*(2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2))) := by
  let D := lambertDiskDerivative (nomePowerScalar a (N+1)) (nomePowerRadius R (N+1))
    (nomePowerRadius_nonneg R hR (N+1)) (nomePowerRadius_local R hR hl (N+1)) (nomePowerScalar_small a R hR ha (N+1))
  let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+2)).derivative a trivial
  let F : Scalar := ⟨nomeLambertPower z R (N+1),nomeLambertPower_valid z R hR hl hz (N+1)⟩
  let G : Scalar := ⟨nomeLambertPower a R (N+1),nomeLambertPower_valid a R hR hl ha (N+1)⟩
  let L : Scalar := ⟨mul D.val M.val,mul_valid D.property M.property⟩
  let v : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  have h := LocalODE.small_scale (Rat.pow_nonneg (n := k) (Rat.natCast_nonneg : (0:Rat)≤((N+2:Nat):Rat)))
    (nomeLambertPower_wide_composition_remainder a z R H hR hl hH ha hz hd N)
  have he := scalar_scaled_remainder F G L v (((N+2:Nat):Rat)^k)
  have hb := Small.congr (scaleRat_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property L.property v.property))
    (SeriesLimitLaws.remainder_valid _ _ _ _ (weightedLambertTerm_valid z R k hR hl hz (N+1))
      (weightedLambertTerm_valid a R k hR hl ha (N+1)) (scaleRat_valid L.property) v.property) (equiv_symm he) h
  have hs := weightedLambertSlope_wide_composition a R k hR hl ha (N+1)
  have hh := FunctionTheory.sub_congr
    (equiv_refl _ (sub_valid (weightedLambertTerm_valid z R k hR hl hz (N+1)) (weightedLambertTerm_valid a R k hR hl ha (N+1))))
    (mul_equiv (scaleRat_valid L.property) (weightedLambertSlope a R k hR hl ha (N+1)).property
      v.property v.property (equiv_symm hs) (equiv_refl _ v.property))
  exact Small.congr
    (SeriesLimitLaws.remainder_valid _ _ _ _ (weightedLambertTerm_valid z R k hR hl hz (N+1))
      (weightedLambertTerm_valid a R k hR hl ha (N+1)) (scaleRat_valid L.property) v.property)
    (SeriesLimitLaws.remainder_valid _ _ _ _ (weightedLambertTerm_valid z R k hR hl hz (N+1))
      (weightedLambertTerm_valid a R k hR hl ha (N+1)) (weightedLambertSlope a R k hR hl ha (N+1)).property v.property) hh hb
end ComputableAnalysis.ModularForms
