import ComputableAnalysis.ModularForms.TauWeightTwoCuspDerivative
import ComputableAnalysis.ModularForms.LambertContinuity
import ComputableAnalysis.RiemannHilbert.MonomialDifference

/-! Actual displacement-sensitive bounds for weight-one Lambert terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Weighted Lambert term variation retains the displacement and degree decay. -/
theorem weightedLambertOneTerm_difference_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hlocal : 4*R≤(1:Rat)/2) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (weightedLambertTerm z R 1 N) (weightedLambertTerm a R 1 N))
      (128*((N+1:Nat):Rat)^2*(2*R)^N*H) := by
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  let D := 2*((N+1:Nat):Rat)*(2*R)^N*H
  have hD : 0≤D := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) Rat.natCast_nonneg) (Rat.pow_nonneg ht)) hH
  have hp := LocalODE.power_difference_bound a.val z.val a.property z.property R H hR hH ha hz hza N
  have hl := lambertFactor_difference_bound (nomePowerScalar a N) (nomePowerScalar z N)
    (nomePowerRadius R N) (nomePowerRadius R N) D
    (nomePowerRadius_nonneg R hR N) (nomePowerRadius_nonneg R hR N) hD
    (nomePowerRadius_local R hR hlocal N) (nomePowerRadius_local R hR hlocal N)
    (nomePowerScalar_small a R hR ha N) (nomePowerScalar_small z R hR hz N) hp
  have h := LocalODE.small_scale (Rat.natCast_nonneg : 0≤((N+1:Nat):Rat)) hl
  have va := nomeLambertPower_valid a R hR hlocal ha N
  have vz := nomeLambertPower_valid z R hR hlocal hz N
  have he : (scaleRat ((N+1:Nat):Rat) (sub (nomeLambertPower z R N) (nomeLambertPower a R N))).Equiv
      (sub (weightedLambertTerm z R 1 N) (weightedLambertTerm a R 1 N)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (sub_valid vz va))
      (hright := sub_valid (weightedLambertTerm_valid z R 1 hR hlocal hz N)
        (weightedLambertTerm_valid a R 1 hR hlocal ha N))
    let Z := ComplexRawQuotient.ofRaw (nomeLambertPower z R N) vz
    let A := ComplexRawQuotient.ofRaw (nomeLambertPower a R N) va
    change ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) (Z+(-A))=
      ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^1) Z-ComplexRawQuotient.scaleRat (((N+1:Nat):Rat)^1) A
    rw [Rat.pow_one,ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_eq_scaleRat_neg_one A,
      ComplexRawQuotient.scaleRat_scaleRat]
    have hc : ((N+1:Nat):Rat)*(-1)= -((N+1:Nat):Rat) := by grind only
    rw [hc,←ComplexRawQuotient.neg_scaleRat]
    rfl
  have hh := Small.congr (scaleRat_valid (sub_valid vz va))
    (sub_valid (weightedLambertTerm_valid z R 1 hR hlocal hz N)
      (weightedLambertTerm_valid a R 1 hR hlocal ha N)) he h
  have hc : ((N+1:Nat):Rat)*(64*D)=128*((N+1:Nat):Rat)^2*(2*R)^N*H := by
    dsimp [D]
    rw [Rat.pow_succ,Rat.pow_one]
    grind only
  rw [hc] at hh
  exact hh

end ComputableAnalysis.ModularForms
