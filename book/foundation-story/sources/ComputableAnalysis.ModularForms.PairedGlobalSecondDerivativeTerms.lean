import ComputableAnalysis.ModularForms.PairedGlobalDerivativeTermsHolomorphic

/-! Actual paired second derivatives and reciprocal-box bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedGlobalSecondDerivativeTerm (n : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  scalarSum (integerReciprocalSecondDerivative (-((n+1:Nat):Int)) z hz)
    (integerReciprocalSecondDerivative ((n+1:Nat):Int) z hz)

theorem pairedGlobalDerivativeTermMap_derivative (n : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((pairedGlobalDerivativeTermMap_holomorphic n).derivative z hz).val.Equiv
      (pairedGlobalSecondDerivativeTerm n z hz).val :=
  add_equiv (integerReciprocalDerivativeMap_derivative _ z hz)
    (integerReciprocalDerivativeMap_derivative _ z hz)

theorem integerReciprocalSecondDerivative_bound (k : Int) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M : Rat) (hM : 0≤M)
    (hs : Small ((integerReciprocalMap k).eval z hz).val M) :
    Small (integerReciprocalSecondDerivative k z hz).val (8*M*M*M) := by
  let i := (integerReciprocalMap k).eval z hz
  have hsq := Small.mul i.property i.property hM hM hs hs
  have hcu := Small.mul i.property (mul_valid i.property i.property) hM
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hM) hs hsq
  exact (LocalODE.small_add hcu hcu).mono (by grind only)

theorem pairedGlobalSecondDerivativeTerm_bound (n : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M : Rat) (hM : 0≤M)
    (hm : Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval z hz).val M)
    (hp : Small ((integerReciprocalMap ((n+1:Nat):Int)).eval z hz).val M) :
    Small (pairedGlobalSecondDerivativeTerm n z hz).val (16*M*M*M) := by
  exact (LocalODE.small_add (integerReciprocalSecondDerivative_bound _ z hz M hM hm)
    (integerReciprocalSecondDerivative_bound _ z hz M hM hp)).mono (by grind only)

theorem pairedGlobalSecondDerivativeTerm_regional_bound (n : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (R : Rat) (hR : 0≤R) (hs : Small z.val R)
    (hlarge : 16*R*R≤pairedIntegerSquare (n+1)) (hRn : R≤((n+1:Nat):Rat)) :
    Small (pairedGlobalSecondDerivativeTerm n z hz).val
      (65536*(1/((n+1:Nat):Rat))*(1/((n+1:Nat):Rat))*(1/((n+1:Nat):Rat))) := by
  have hm := upperIntegerReciprocal_minus_bound z hz R hR hs (n+1) (by omega) hlarge hRn
  have hp := upperIntegerReciprocal_plus_bound z hz R hR hs (n+1) (by omega) hlarge hRn
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hM : 0≤16*(1/((n+1:Nat):Rat)) := by
    rw [Rat.div_def,Rat.one_mul]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  exact (pairedGlobalSecondDerivativeTerm_bound n z hz _ hM hm hp).mono (by grind only)

end ComputableAnalysis.ModularForms
