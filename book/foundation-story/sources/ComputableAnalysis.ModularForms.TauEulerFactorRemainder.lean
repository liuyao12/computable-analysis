import ComputableAnalysis.ModularForms.TauEulerDerivativeLimit
import ComputableAnalysis.RiemannHilbert.MonomialRemainder

/-! Exact finite remainders of actual Euler factors at represented inputs. -/
set_option maxHeartbeats 800000
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The actual analytic remainder of the base Euler factor is the negative
literal monomial remainder, including its affine case. -/
theorem tauEulerFactorMap_remainder_identity (a z : Scalar) (N : Nat) :
    (DomainFunctions.remainder (tauEulerFactorMap N) a trivial
      ((tauEulerFactorMap_holomorphic N).derivative a trivial) z trivial).Equiv
      (neg (LocalODE.monomialRemainder a.val z.val (N+1))) := by
  let D := (tauEulerFactorMap_holomorphic N).derivative a trivial
  have hS := LocalODE.monomialSlope_valid a.val a.property (N+1)
  have hP := LocalODE.power_valid a.val a.property N
  have hd : D.val.Equiv (neg (LocalODE.monomialSlope a.val (N+1))) :=
    equiv_trans D.property (neg_valid (scaleRat_valid hP)) (neg_valid hS)
      (tauEulerFactorMap_derivative a N)
      (neg_equiv (equiv_symm (LocalODE.monomialSlope_formula a.val a.property N)))
  have hdc := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := D.property) (hright := neg_valid hS) hd
  have hm := LocalODE.monomial_decomposition a.val z.val a.property z.property (N+1)
  have hR := LocalODE.monomialRemainder_valid a.val z.val a.property z.property (N+1)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (LocalODE.monomialSlope a.val (N+1)) hS
  let R := ComplexRawQuotient.ofRaw (LocalODE.monomialRemainder a.val z.val (N+1)) hR
  let AP := ComplexRawQuotient.ofRaw (LocalODE.power a.val (N+1)) (LocalODE.power_valid _ a.property _)
  let ZP := ComplexRawQuotient.ofRaw (LocalODE.power z.val (N+1)) (LocalODE.power_valid _ z.property _)
  let d := ComplexRawQuotient.ofRaw D.val D.property
  change d = -S at hdc
  change ZP=AP+S*(Z-A)+R at hm
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := DomainFunctions.remainder_valid (tauEulerFactorMap N) a trivial D z trivial) (hright := neg_valid hR)
  change ((1-ZP)-(1-AP))-d*(Z-A)= -R
  rw [hdc,hm]
  grind only

/-- The degree-one base factor has exact zero remainder. -/
theorem tauEulerFactorMap_affine_remainder (a z : Scalar) :
    Small (DomainFunctions.remainder (tauEulerFactorMap 0) a trivial
      ((tauEulerFactorMap_holomorphic 0).derivative a trivial) z trivial) 0 := by
  have h := SeriesLimitLaws.small_neg (LocalODE.monomialRemainder_one_small a.val z.val a.property z.property)
  exact Small.congr (neg_valid (LocalODE.monomialRemainder_valid _ _ a.property z.property 1))
    (DomainFunctions.remainder_valid _ _ _ _ _ _) (equiv_symm (tauEulerFactorMap_remainder_identity a z 0)) h

/-- A displacement-sensitive quadratic error for every higher base factor. -/
theorem tauEulerFactorMap_quadratic_remainder_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hH : 0≤H) (ha : Small a.val R) (hz : Small z.val R)
    (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (tauEulerFactorMap (N+1)) a trivial
      ((tauEulerFactorMap_holomorphic (N+1)).derivative a trivial) z trivial)
      (2*((N+2:Nat):Rat)*((N+1:Nat):Rat)*(2*R)^N*H^2) := by
  have h := SeriesLimitLaws.small_neg
    (LocalODE.monomialRemainder_bound a.val z.val a.property z.property R H hR hH ha hz hza N)
  exact Small.congr (neg_valid (LocalODE.monomialRemainder_valid _ _ a.property z.property (N+2)))
    (DomainFunctions.remainder_valid _ _ _ _ _ _) (equiv_symm (tauEulerFactorMap_remainder_identity a z (N+1))) h

end ComputableAnalysis.ModularForms
