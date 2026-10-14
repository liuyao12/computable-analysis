import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTail

/-! Holomorphic maps for actual reciprocal-cube second-derivative terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def reciprocalCubeMap (k : Int) : DomainFunctions.Map :=
  productOn (integerReciprocalMap k)
    (productOn (integerReciprocalMap k) (integerReciprocalMap k)
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

private def reciprocalCubeMap_holomorphic (k : Int) : Holomorphic (reciprocalCubeMap k) :=
  (integerReciprocalMap_holomorphic k).productOn
    ((integerReciprocalMap_holomorphic k).productOn (integerReciprocalMap_holomorphic k)
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def integerReciprocalSecondDerivativeMap (k : Int) : DomainFunctions.Map :=
  sumOn (reciprocalCubeMap k) (reciprocalCubeMap k)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def integerReciprocalSecondDerivativeMap_holomorphic (k : Int) : Holomorphic (integerReciprocalSecondDerivativeMap k) :=
  (reciprocalCubeMap_holomorphic k).sumOn (reciprocalCubeMap_holomorphic k)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def pairedGlobalSecondDerivativeTermMap (n : Nat) : DomainFunctions.Map :=
  sumOn (integerReciprocalSecondDerivativeMap (-((n+1:Nat):Int)))
    (integerReciprocalSecondDerivativeMap ((n+1:Nat):Int))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def pairedGlobalSecondDerivativeTermMap_holomorphic (n : Nat) : Holomorphic (pairedGlobalSecondDerivativeTermMap n) :=
  (integerReciprocalSecondDerivativeMap_holomorphic (-((n+1:Nat):Int))).sumOn
    (integerReciprocalSecondDerivativeMap_holomorphic ((n+1:Nat):Int))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

theorem pairedGlobalSecondDerivativeTermMap_eval (n : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedGlobalSecondDerivativeTermMap n).eval z hz).val = (pairedGlobalSecondDerivativeTerm n z hz).val := rfl

theorem integerReciprocalSecondDerivativeMap_eval (k : Int) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalSecondDerivativeMap k).eval z hz).val = (integerReciprocalSecondDerivative k z hz).val := rfl

end ComputableAnalysis.ModularForms
