import ComputableAnalysis.ModularForms.PairedDerivativeTail
import ComputableAnalysis.ModularForms.SymmetricReciprocalPrefixes
import ComputableAnalysis.ModularForms.UpperReciprocalDerivative
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums
import ComputableAnalysis.RiemannHilbert.DomainDerivativeInvariance

/-! Actual derivatives of the paired terms whose derivative tails have been constructed. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem integerReciprocalVector_nonzero (k : Int) :
    (⟨k,1⟩ : QuadraticOrder163)≠QuadraticOrder163.zero := by
  intro h
  have hy := congrArg QuadraticOrder163.y h
  change (1:Int)=0 at hy
  omega

def integerReciprocalMap (k : Int) : DomainFunctions.Map :=
  latticeReciprocalMap ⟨k,1⟩ (integerReciprocalVector_nonzero k)

def integerReciprocalMap_holomorphic (k : Int) : DomainFunctions.Holomorphic (integerReciprocalMap k) :=
  latticeReciprocalMap_holomorphic ⟨k,1⟩ (integerReciprocalVector_nonzero k)

theorem integerReciprocalMap_eval (k : Int) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalMap k).eval z hz).val=(upperIntegerReciprocal z hz k).val := rfl

theorem integerReciprocalMap_derivative (k : Int) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((integerReciprocalMap_holomorphic k).derivative z hz).val.Equiv
      (ReciprocalDifference.derivative (integerShiftScalar z k)
        (upperScalar_nonzero _ (integerShiftScalar_upper z hz k))).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((integerReciprocalMap_holomorphic k).derivative z hz).property)
    (hright := (ReciprocalDifference.derivative (integerShiftScalar z k)
      (upperScalar_nonzero _ (integerShiftScalar_upper z hz k))).property)
  let I := ComplexRawQuotient.ofRaw (upperIntegerReciprocal z hz k).val
    (upperIntegerReciprocal z hz k).property
  change (-(I*I))*1= -(I*I)
  grind only

def pairedReciprocalTermMap (n : Nat) : DomainFunctions.Map :=
  sumOn (integerReciprocalMap (-((n+1:Nat):Int)))
    (integerReciprocalMap ((n+1:Nat):Int)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def pairedReciprocalTermMap_holomorphic (n : Nat) : DomainFunctions.Holomorphic (pairedReciprocalTermMap n) :=
  (integerReciprocalMap_holomorphic (-((n+1:Nat):Int))).sumOn
    (integerReciprocalMap_holomorphic ((n+1:Nat):Int)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

theorem pairedReciprocalTermMap_eval_agreement (n : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((pairedReciprocalTermMap n).eval z hz).val.Equiv (upperPairedLatticeTerm z hz n).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((pairedReciprocalTermMap n).eval z hz).property)
    (hright := (upperPairedLatticeTerm z hz n).property)
  exact (upperPairedLatticeTerm_class z hz n).symm

theorem pairedReciprocalTermMap_derivative (n : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedReciprocalTermMap_holomorphic n).derivative z hz).val.Equiv
      (upperPairedReciprocalDerivative z hz (n+1)).val := by
  have hm := ReciprocalDifference.derivative_congr
    (integerShiftScalar z (-((n+1:Nat):Int))) (pairedMinus z (boundaryIntegerScalar (n+1)))
    (upperScalar_nonzero _ (integerShiftScalar_upper z hz _))
    (upperShiftMinus_nonzero z hz ((n+1:Nat):Rat)) (integerShiftScalar_minus z (n+1))
  have hp := ReciprocalDifference.derivative_congr
    (integerShiftScalar z ((n+1:Nat):Int)) (pairedPlus z (boundaryIntegerScalar (n+1)))
    (upperScalar_nonzero _ (integerShiftScalar_upper z hz _))
    (upperShiftPlus_nonzero z hz ((n+1:Nat):Rat)) (integerShiftScalar_plus z (n+1))
  exact add_equiv
    (equiv_trans ((integerReciprocalMap_holomorphic (-((n+1:Nat):Int))).derivative z hz).property
      (ReciprocalDifference.derivative (integerShiftScalar z (-((n+1:Nat):Int)))
        (upperScalar_nonzero _ (integerShiftScalar_upper z hz _))).property
      (ReciprocalDifference.derivative (pairedMinus z (boundaryIntegerScalar (n+1)))
        (upperShiftMinus_nonzero z hz ((n+1:Nat):Rat))).property
      (integerReciprocalMap_derivative _ z hz) hm)
    (equiv_trans ((integerReciprocalMap_holomorphic ((n+1:Nat):Int)).derivative z hz).property
      (ReciprocalDifference.derivative (integerShiftScalar z ((n+1:Nat):Int))
        (upperScalar_nonzero _ (integerShiftScalar_upper z hz _))).property
      (ReciprocalDifference.derivative (pairedPlus z (boundaryIntegerScalar (n+1)))
        (upperShiftPlus_nonzero z hz ((n+1:Nat):Rat))).property
      (integerReciprocalMap_derivative _ z hz) hp)

def pairedReciprocalTermMap_hasDerivativeAt (n : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) : HasDerivativeAt (pairedReciprocalTermMap n) z hz
      (upperPairedReciprocalDerivative z hz (n+1)) :=
  ((pairedReciprocalTermMap_holomorphic n).atPoint z hz).congrDerivative
    (pairedReciprocalTermMap_derivative n z hz)

end ComputableAnalysis.ModularForms
