import ComputableAnalysis.ModularForms.LambertWideWeightedRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem nomeLambertPower_wide_first_remainder_bound (a z : Scalar)
    (R : Rat) (hR : 0≤R) (hl : 4*R≤(1:Rat)/2) (ha : Small a.val R) (hz : Small z.val R)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) :
    let D := lambertDiskDerivative (nomePowerScalar a 0) (nomePowerRadius R 0)
      (nomePowerRadius_nonneg R hR 0)
      (nomePowerRadius_local R hR hl 0)
      (nomePowerScalar_small a R hR ha 0)
    let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic 1).derivative a trivial
    Small (SeriesLimitLaws.remainder (nomeLambertPower z R 0)
      (nomeLambertPower a R 0) (mul D.val M.val) (sub z.val a.val))
      (4096*H^2) := by
  intro D M
  let A := nomePowerScalar a 0
  let Z := nomePowerScalar z 0
  let F : Scalar := ⟨nomeLambertPower z R 0,nomeLambertPower_valid z R hR hl hz 0⟩
  let G : Scalar := ⟨nomeLambertPower a R 0,nomeLambertPower_valid a R hR hl ha 0⟩
  have ho := tauLambertPower_outer_remainder_bound a z R H
    hR hl hH ha
    hz hd 0
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
    (by decide +kernel : (0:Rat)≤32) (Rat.le_refl : (0:Rat)≤0) (lambertDiskDerivative_bound _ _ _ _ _) hi
  have hs := LocalODE.small_add hob hm
  let v : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  have hc := scalar_composition_remainder F G A Z D M v
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


theorem weightedLambertTerm_wide_first_remainder_bound (k : Nat) (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hl : 4*R≤(1:Rat)/2) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hd : Small (sub z.val a.val) H) :
    Small (SeriesLimitLaws.remainder (weightedLambertTerm z R k 0)
      (weightedLambertTerm a R k 0) (weightedLambertSlope a R k hR hl ha 0).val (sub z.val a.val))
      (4096*H^2) := by
  let D := lambertDiskDerivative (nomePowerScalar a 0) (nomePowerRadius R 0)
    (nomePowerRadius_nonneg R hR 0) (nomePowerRadius_local R hR hl 0) (nomePowerScalar_small a R hR ha 0)
  let M := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic 1).derivative a trivial
  let F : Scalar := ⟨nomeLambertPower z R 0,nomeLambertPower_valid z R hR hl hz 0⟩
  let G : Scalar := ⟨nomeLambertPower a R 0,nomeLambertPower_valid a R hR hl ha 0⟩
  let L : Scalar := ⟨mul D.val M.val,mul_valid D.property M.property⟩
  let v : Scalar := ⟨sub z.val a.val,sub_valid z.property a.property⟩
  have h := LocalODE.small_scale (Rat.pow_nonneg (n := k) (Rat.natCast_nonneg : (0:Rat)≤(1:Rat)))
    (nomeLambertPower_wide_first_remainder_bound a z R hR hl ha hz H hH hd)
  have he := scalar_scaled_remainder F G L v ((1:Rat)^k)
  have hb := Small.congr (scaleRat_valid (SeriesLimitLaws.remainder_valid _ _ _ _ F.property G.property L.property v.property))
    (SeriesLimitLaws.remainder_valid _ _ _ _ (weightedLambertTerm_valid z R k hR hl hz 0)
      (weightedLambertTerm_valid a R k hR hl ha 0) (scaleRat_valid L.property) v.property) (equiv_symm he) h
  have hs := weightedLambertSlope_wide_composition a R k hR hl ha 0
  have hh := FunctionTheory.sub_congr
    (equiv_refl _ (sub_valid (weightedLambertTerm_valid z R k hR hl hz 0) (weightedLambertTerm_valid a R k hR hl ha 0)))
    (mul_equiv (scaleRat_valid L.property) (weightedLambertSlope a R k hR hl ha 0).property
      v.property v.property (equiv_symm hs) (equiv_refl _ v.property))
  have hfinal := Small.congr
    (SeriesLimitLaws.remainder_valid _ _ _ _ (weightedLambertTerm_valid z R k hR hl hz 0)
      (weightedLambertTerm_valid a R k hR hl ha 0) (scaleRat_valid L.property) v.property)
    (SeriesLimitLaws.remainder_valid _ _ _ _ (weightedLambertTerm_valid z R k hR hl hz 0)
      (weightedLambertTerm_valid a R k hR hl ha 0) (weightedLambertSlope a R k hR hl ha 0).property v.property) hh hb
  have hone (j : Nat) : (1:Rat)^j=1 := by
    induction j with
    | zero => rfl
    | succ k ih => rw [Rat.pow_succ,ih]; exact Rat.one_mul 1
  simpa only [show ((1:Nat):Rat)=(1:Rat) from rfl,hone k,Rat.one_mul,v] using hfinal

end ComputableAnalysis.ModularForms
