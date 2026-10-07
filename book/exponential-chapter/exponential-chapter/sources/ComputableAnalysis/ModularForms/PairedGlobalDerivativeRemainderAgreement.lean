import ComputableAnalysis.ModularForms.PairedGlobalDerivativeRemainderBound

/-! Exact agreement of the paired quadratic expression with its analytic remainder. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalDerivativeTermMap_remainder (n : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (DomainFunctions.remainder (pairedGlobalDerivativeTermMap n) a ha
      (pairedGlobalSecondDerivativeTerm n a ha) z hz).Equiv
      (pairedGlobalDerivativeRemainder n a z ha hz).val := by
  have he := sum_remainder
    (integerReciprocalDerivativeMap (-((n+1:Nat):Int)))
    (integerReciprocalDerivativeMap ((n+1:Nat):Int))
    (fun (w : Scalar) (hw : InUpperHalfPlane w.val) => hw) a ha
    (integerReciprocalSecondDerivative (-((n+1:Nat):Int)) a ha)
    (integerReciprocalSecondDerivative ((n+1:Nat):Int) a ha) z hz
  exact equiv_trans (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (add_valid (DomainFunctions.remainder_valid _ _ _ _ _ _)
      (DomainFunctions.remainder_valid _ _ _ _ _ _))
    (pairedGlobalDerivativeRemainder n a z ha hz).property he
    (add_equiv (integerReciprocalDerivativeMap_remainder _ a z ha hz)
      (integerReciprocalDerivativeMap_remainder _ a z ha hz))

end ComputableAnalysis.ModularForms
