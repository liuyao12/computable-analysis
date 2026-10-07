import ComputableAnalysis.ModularForms.PairedSecondDerivativeTermsHolomorphic

/-! Holomorphic finite derivative sums and their exact second derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedSecondDerivativeTailPrefixMap (B N : Nat) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨ScalarSeries.block (fun n => ((pairedGlobalSecondDerivativeTermMap (4*B+n)).eval z hz).val) 0 N,
    ScalarSeries.block_valid _ (fun n => ((pairedGlobalSecondDerivativeTermMap (4*B+n)).eval z hz).property) 0 N⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := ScalarSeries.block_congr _ _
    (fun n => (pairedGlobalSecondDerivativeTermMap (4*B+n)).eval_congr z w hz hw he) 0 N

def pairedSecondDerivativeTailPrefixMap_holomorphic (B N : Nat) : DomainFunctions.Holomorphic (pairedSecondDerivativeTailPrefixMap B N) := by
  induction N with
  | zero =>
    apply (constantOn_holomorphic upperOpenData ⟨zero,ofQComplex_valid _⟩).transfer
      (pairedSecondDerivativeTailPrefixMap B 0) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    have h := ih.sumOn (pairedGlobalSecondDerivativeTermMap_holomorphic (4*B+N))
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
    apply h.transfer (pairedSecondDerivativeTailPrefixMap B (N+1)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    simp only [sumOn,pairedSecondDerivativeTailPrefixMap,scalarSum,ScalarSeries.block.eq_2,Nat.zero_add]
    exact equiv_refl _ (add_valid
      (ScalarSeries.block_valid _ (fun n => ((pairedGlobalSecondDerivativeTermMap (4*B+n)).eval z hz).property) 0 N)
      ((pairedGlobalSecondDerivativeTermMap (4*B+N)).eval z hz).property)

theorem pairedSecondDerivativeTailPrefixMap_eval (B N : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedSecondDerivativeTailPrefixMap B N).eval z hz).val.Equiv
      (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm (4*B+n) z hz).val) 0 N) :=
  ScalarSeries.block_congr _ _
    (fun n => (pairedGlobalSecondDerivativeTermMap_eval (4*B+n) z hz) ▸
      equiv_refl _ (pairedGlobalSecondDerivativeTerm (4*B+n) z hz).property) 0 N

end ComputableAnalysis.ModularForms
