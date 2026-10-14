import ComputableAnalysis.ModularForms.PairedIntegerPoleExtension
import ComputableAnalysis.ModularForms.PairedReciprocalTermHolomorphic

/-! Actual integer reciprocal functions on their full off-pole domains. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions NonzeroBoxSearch

def integerReciprocalOffPoleMap (k : Int) : DomainFunctions.Map :=
  compose ReciprocalHolomorphic.function (entireIntegerShiftMap k)

def integerReciprocalOffPoleMap_holomorphic (k : Int) :
    Holomorphic (integerReciprocalOffPoleMap k) :=
  ReciprocalHolomorphic.holomorphic.compose (entireIntegerShiftMap_holomorphic k)

theorem integerReciprocalOffPoleMap_domain (k : Int) (z : Scalar) :
    (integerReciprocalOffPoleMap k).domain z ↔ Nonzero (integerShiftScalar z k) := by
  constructor
  · intro hz
    exact compose_outer_mem hz
  · intro hz
    exact ⟨trivial,hz⟩

theorem integerReciprocalOffPoleMap_upper_mem (k : Int) (z : Scalar)
    (hz : InUpperHalfPlane z.val) : (integerReciprocalOffPoleMap k).domain z :=
  (integerReciprocalOffPoleMap_domain k z).mpr
    (upperScalar_nonzero (integerShiftScalar z k) (integerShiftScalar_upper z hz k))

theorem integerReciprocalOffPoleMap_upper_agreement (k : Int) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalOffPoleMap k).eval z (integerReciprocalOffPoleMap_upper_mem k z hz)).val.Equiv
      ((integerReciprocalMap k).eval z hz).val := by
  exact equiv_refl _ ((integerReciprocalMap k).eval z hz).property


theorem integerReciprocalOffPoleMap_derivative (k : Int) (z : Scalar)
    (hz : (integerReciprocalOffPoleMap k).domain z) :
    ((integerReciprocalOffPoleMap_holomorphic k).derivative z hz).val.Equiv
      (neg (mul ((integerReciprocalOffPoleMap k).eval z hz).val
        ((integerReciprocalOffPoleMap k).eval z hz).val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((integerReciprocalOffPoleMap_holomorphic k).derivative z hz).property)
    (hright := neg_valid (mul_valid ((integerReciprocalOffPoleMap k).eval z hz).property
      ((integerReciprocalOffPoleMap k).eval z hz).property))
  let I := ComplexRawQuotient.ofRaw ((integerReciprocalOffPoleMap k).eval z hz).val
    ((integerReciprocalOffPoleMap k).eval z hz).property
  change (-(I*I))*1= -(I*I)
  grind only

theorem integerReciprocalOffPoleMap_upper_derivative_agreement (k : Int) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalOffPoleMap_holomorphic k).derivative z
      (integerReciprocalOffPoleMap_upper_mem k z hz)).val.Equiv
      ((integerReciprocalMap_holomorphic k).derivative z hz).val := by
  have h := integerReciprocalOffPoleMap_derivative k z (integerReciprocalOffPoleMap_upper_mem k z hz)
  exact equiv_trans
    ((integerReciprocalOffPoleMap_holomorphic k).derivative z (integerReciprocalOffPoleMap_upper_mem k z hz)).property
    (neg_valid (mul_valid ((integerReciprocalMap k).eval z hz).property ((integerReciprocalMap k).eval z hz).property))
    ((integerReciprocalMap_holomorphic k).derivative z hz).property h
    (equiv_symm (integerReciprocalMap_derivative k z hz))


def integerReciprocalOffPoleDerivativeMap (k : Int) : DomainFunctions.Map :=
  negate (productOn (integerReciprocalOffPoleMap k) (integerReciprocalOffPoleMap k)
    (fun _ hz => hz))

def integerReciprocalOffPoleDerivativeMap_holomorphic (k : Int) :
    Holomorphic (integerReciprocalOffPoleDerivativeMap k) :=
  ((integerReciprocalOffPoleMap_holomorphic k).productOn
    (integerReciprocalOffPoleMap_holomorphic k) (fun _ hz => hz)).negate

def integerReciprocalOffPoleMap_hasDerivativeAt (k : Int) (z : Scalar)
    (hz : (integerReciprocalOffPoleMap k).domain z) :
    HasDerivativeAt (integerReciprocalOffPoleMap k) z hz
      ((integerReciprocalOffPoleDerivativeMap k).eval z hz) :=
  ((integerReciprocalOffPoleMap_holomorphic k).atPoint z hz).congrDerivative
    (integerReciprocalOffPoleMap_derivative k z hz)

end ComputableAnalysis.ModularForms
