import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTerms

/-! Holomorphic finite derivative sums and their exact second derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedFiniteDerivativeMap (N : Nat) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).val) 0 N,
    ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) 0 N⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := ScalarSeries.block_congr _ _
    (fun n => (pairedGlobalDerivativeTermMap n).eval_congr z w hz hw he) 0 N

def pairedFiniteDerivativeMap_holomorphic (N : Nat) : DomainFunctions.Holomorphic (pairedFiniteDerivativeMap N) := by
  induction N with
  | zero =>
    apply (constantOn_holomorphic upperOpenData ⟨zero,ofQComplex_valid _⟩).transfer
      (pairedFiniteDerivativeMap 0) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    have h := ih.sumOn (pairedGlobalDerivativeTermMap_holomorphic N)
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
    apply h.transfer (pairedFiniteDerivativeMap (N+1)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    simp only [sumOn,pairedFiniteDerivativeMap,scalarSum,ScalarSeries.block.eq_2,Nat.zero_add]
    exact equiv_refl _ (add_valid
      (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) 0 N)
      ((pairedGlobalDerivativeTermMap N).eval z hz).property)

theorem pairedFiniteDerivativeMap_eval (N : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedFiniteDerivativeMap N).eval z hz).val.Equiv
      (ScalarSeries.block (fun n => (upperPairedReciprocalDerivative z hz (n+1)).val) 0 N) :=
  ScalarSeries.block_congr _ _ (fun n => pairedGlobalDerivativeTermMap_eval n z hz) 0 N

theorem pairedFiniteDerivativeMap_derivative (N : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedFiniteDerivativeMap_holomorphic N).derivative z hz).val.Equiv
      (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm n z hz).val) 0 N) := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    simp only [ScalarSeries.block.eq_2,Nat.zero_add]
    exact add_equiv ih (pairedGlobalDerivativeTermMap_derivative N z hz)

end ComputableAnalysis.ModularForms
