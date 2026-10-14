import ComputableAnalysis.ModularForms.TauLambertOuterRemainder
import ComputableAnalysis.RiemannHilbert.MonomialRemainder

/-! Quadratic bounds for the actual inner monomial remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauCoordinatePower_actual_remainder_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hH : 0≤H) (ha : Small a.val R) (hz : Small z.val R)
    (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (SeriesLimitLaws.remainder (LocalODE.power z.val (N+2))
      (LocalODE.power a.val (N+2))
      ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+2)).derivative a trivial).val
      (sub z.val a.val)) (2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2) := by
  let D := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+2)).derivative a trivial
  have he : D.val.Equiv (LocalODE.monomialSlope a.val (N+2)) :=
    equiv_trans D.property (scaleRat_valid (LocalODE.power_valid _ a.property (N+1)))
      (LocalODE.monomialSlope_valid _ a.property (N+2))
      (tauCoordinatePower_derivative a (N+1))
      (equiv_symm (LocalODE.monomialSlope_formula a.val a.property (N+1)))
  have hi := FunctionTheory.sub_congr
    (equiv_refl (sub (LocalODE.power z.val (N+2)) (LocalODE.power a.val (N+2)))
      (sub_valid (LocalODE.power_valid _ z.property _) (LocalODE.power_valid _ a.property _)))
    (mul_equiv D.property (LocalODE.monomialSlope_valid _ a.property (N+2))
      (sub_valid z.property a.property) (sub_valid z.property a.property) he
      (equiv_refl _ (sub_valid z.property a.property)))
  have hid := equiv_trans
    (SeriesLimitLaws.remainder_valid _ _ _ _ (LocalODE.power_valid _ z.property _)
      (LocalODE.power_valid _ a.property _) D.property (sub_valid z.property a.property))
    (sub_valid (sub_valid (LocalODE.power_valid _ z.property _) (LocalODE.power_valid _ a.property _))
      (mul_valid (LocalODE.monomialSlope_valid _ a.property (N+2)) (sub_valid z.property a.property)))
    (LocalODE.monomialRemainder_valid _ _ a.property z.property (N+2)) hi
    (LocalODE.monomial_remainder_identity a.val z.val a.property z.property (N+2))
  exact Small.congr (LocalODE.monomialRemainder_valid _ _ a.property z.property (N+2))
    (SeriesLimitLaws.remainder_valid _ _ _ _ (LocalODE.power_valid _ z.property _)
      (LocalODE.power_valid _ a.property _) D.property (sub_valid z.property a.property))
    (equiv_symm hid) (LocalODE.monomialRemainder_bound a.val z.val a.property z.property R H hR hH ha hz hd N)

/-- The first monomial has exactly zero actual first-order remainder. -/
theorem tauCoordinatePower_first_remainder_zero (a z : Scalar) :
    (SeriesLimitLaws.remainder (LocalODE.power z.val 1) (LocalODE.power a.val 1)
      ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic 1).derivative a trivial).val
      (sub z.val a.val)).Equiv zero := by
  let D := (tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic 1).derivative a trivial
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := D.property)
    (hright := scaleRat_valid (LocalODE.power_valid _ a.property 0)) (tauCoordinatePower_derivative a 0)
  let d := ComplexRawQuotient.ofRaw D.val D.property
  have he : d=1 := by
    change d=ComplexRawQuotient.scaleRat 1 1 at hd
    rw [ComplexRawQuotient.scaleRat_one] at hd
    exact hd
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := SeriesLimitLaws.remainder_valid _ _ _ _ (LocalODE.power_valid _ z.property 1)
      (LocalODE.power_valid _ a.property 1) D.property (sub_valid z.property a.property))
    (hright := ofQComplex_valid _)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change (1*Z-1*A)-d*(Z-A)=0
  rw [he]
  grind only

end ComputableAnalysis.ModularForms
