import ComputableAnalysis.ModularForms.PairedReciprocalTermHolomorphic

/-! Holomorphic actual reciprocal derivative terms on the full upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def integerReciprocalDerivativeMap (k : Int) : DomainFunctions.Map :=
  negate (productOn (integerReciprocalMap k) (integerReciprocalMap k) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))

def integerReciprocalDerivativeMap_holomorphic (k : Int) : Holomorphic (integerReciprocalDerivativeMap k) :=
  ((integerReciprocalMap_holomorphic k).productOn (integerReciprocalMap_holomorphic k) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)).negate

theorem integerReciprocalDerivativeMap_eval (k : Int) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalDerivativeMap k).eval z hz).val.Equiv
      ((integerReciprocalMap_holomorphic k).derivative z hz).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((integerReciprocalDerivativeMap k).eval z hz).property)
    (hright := ((integerReciprocalMap_holomorphic k).derivative z hz).property)
  let I := ComplexRawQuotient.ofRaw ((integerReciprocalMap k).eval z hz).val
    ((integerReciprocalMap k).eval z hz).property
  change -(I*I)=(-(I*I))*1
  grind only

def pairedGlobalDerivativeTermMap (n : Nat) : DomainFunctions.Map :=
  sumOn (integerReciprocalDerivativeMap (-((n+1:Nat):Int)))
    (integerReciprocalDerivativeMap ((n+1:Nat):Int)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def pairedGlobalDerivativeTermMap_holomorphic (n : Nat) : Holomorphic (pairedGlobalDerivativeTermMap n) :=
  (integerReciprocalDerivativeMap_holomorphic (-((n+1:Nat):Int))).sumOn
    (integerReciprocalDerivativeMap_holomorphic ((n+1:Nat):Int)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

theorem pairedGlobalDerivativeTermMap_eval (n : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedGlobalDerivativeTermMap n).eval z hz).val.Equiv
      (upperPairedReciprocalDerivative z hz (n+1)).val :=
  equiv_trans ((pairedGlobalDerivativeTermMap n).eval z hz).property
    ((pairedReciprocalTermMap_holomorphic n).derivative z hz).property
    (upperPairedReciprocalDerivative z hz (n+1)).property
    (add_equiv (integerReciprocalDerivativeMap_eval _ z hz) (integerReciprocalDerivativeMap_eval _ z hz))
    (pairedReciprocalTermMap_derivative n z hz)

def integerReciprocalSecondDerivative (k : Int) (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  let i := (integerReciprocalMap k).eval z hz
  let c := DomainFunctions.scalarProduct i (DomainFunctions.scalarProduct i i)
  scalarSum c c

theorem integerReciprocalDerivativeMap_derivative (k : Int) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalDerivativeMap_holomorphic k).derivative z hz).val.Equiv
      (integerReciprocalSecondDerivative k z hz).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((integerReciprocalDerivativeMap_holomorphic k).derivative z hz).property)
    (hright := (integerReciprocalSecondDerivative k z hz).property)
  let I := ComplexRawQuotient.ofRaw ((integerReciprocalMap k).eval z hz).val
    ((integerReciprocalMap k).eval z hz).property
  change -(((-(I*I))*1)*I+I*((-(I*I))*1)) = I*(I*I)+I*(I*I)
  grind only

end ComputableAnalysis.ModularForms
