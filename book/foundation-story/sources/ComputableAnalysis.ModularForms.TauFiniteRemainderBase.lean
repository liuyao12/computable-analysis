import ComputableAnalysis.ModularForms.TauFiniteQuadraticStep

/-! Constructed base cases for finite Euler-product quadratic remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem finiteDiscriminantEulerRemainder_zero (a z : Scalar) :
    (finiteDiscriminantEulerRemainder a z 0).val.Equiv zero := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (finiteDiscriminantEulerRemainder a z 0).property)
    (hright := ofQComplex_valid _)
  let h := ComplexRawQuotient.ofRaw (sub z.val a.val) (sub_valid z.property a.property)
  change (1-1)-0*h=0
  grind only

/-- The first whole-product remainder equals the actual first-factor remainder. -/
theorem finiteDiscriminantEulerRemainder_one (a z : Scalar) :
    (finiteDiscriminantEulerRemainder a z 1).val.Equiv
      (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap 0) 24) a trivial
        ((tauMapPower_holomorphic (tauEulerFactorMap 0)
          (tauEulerFactorMap_holomorphic 0) 24).derivative a trivial) z trivial) := by
  let F := tauEulerFactorValue a 0
  let G := tauEulerFactorValue z 0
  let E := tauEulerFactorSlope a 0
  let A := (tauMapPower_holomorphic (tauEulerFactorMap 0)
    (tauEulerFactorMap_holomorphic 0) 24).derivative a trivial
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := A.property)
    (hright := E.property) (tauEulerFactorSlope_actual a 0)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (finiteDiscriminantEulerRemainder a z 1).property)
    (hright := DomainFunctions.remainder_valid _ _ _ _ _ _)
  let f := ComplexRawQuotient.ofRaw F.val F.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  let e := ComplexRawQuotient.ofRaw E.val E.property
  let av := ComplexRawQuotient.ofRaw A.val A.property
  let h := ComplexRawQuotient.ofRaw (sub z.val a.val) (sub_valid z.property a.property)
  change av=e at hd
  change (1*g-1*f)-(0*f+1*e)*h=(g-f)-av*h
  rw [hd]
  grind only

/-- Quadratic propagation starts with a constructed first-product bound. -/
theorem finiteDiscriminantEulerRemainder_one_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/512) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) :
    Small (finiteDiscriminantEulerRemainder a z 1).val (tauEulerFactorRemainderConstant*H^2) :=
  Small.congr (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (finiteDiscriminantEulerRemainder a z 1).property
    (equiv_symm (finiteDiscriminantEulerRemainder_one a z))
    (tauEulerFirstFactorPower_geometric_remainder_bound a z R H hR hRMax hH ha hz hza)

/-- Executable quadratic constants for the positive finite products. -/
def tauEulerQuadraticBudget (R : Rat) : Nat → Rat
  | 0 => tauEulerFactorRemainderConstant
  | N+1 => tauEulerQuadraticBudget R N+
      96*tauEulerQuadraticBudget R N*(2*R)^(N+2)+
      4*tauEulerFactorRemainderConstant*(8*R)^N+
      786432*(4:Rat)^23*(4*R)^(N+1)

theorem tauEulerQuadraticBudget_nonnegative (R : Rat) (hR : 0≤R) (N : Nat) :
    0≤tauEulerQuadraticBudget R N := by
  have hc : 0≤tauEulerFactorRemainderConstant := by decide +kernel
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hu : 0≤4*R := Rat.mul_nonneg (by decide +kernel) hR
  have hv : 0≤8*R := Rat.mul_nonneg (by decide +kernel) hR
  induction N with
  | zero => exact hc
  | succ N ih =>
    exact Rat.add_nonneg (Rat.add_nonneg (Rat.add_nonneg ih
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) ih) (Rat.pow_nonneg ht)))
      (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hc) (Rat.pow_nonneg hv)))
      (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hu))

/-- Every positive finite product has a constructed quadratic remainder bound. -/
theorem finiteDiscriminantEulerRemainder_budget_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/1024) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (finiteDiscriminantEulerRemainder a z (N+1)).val (tauEulerQuadraticBudget R N*H^2) := by
  induction N with
  | zero =>
    exact finiteDiscriminantEulerRemainder_one_bound a z R H hR
      (Rat.le_trans hRMax (by decide +kernel)) hH ha hz hza
  | succ N ih =>
    exact finiteDiscriminantEulerRemainder_quadratic_step a z R H
      (tauEulerQuadraticBudget R N) hR hRMax hH (tauEulerQuadraticBudget_nonnegative R hR N)
      ha hz hza N ih

end ComputableAnalysis.ModularForms
