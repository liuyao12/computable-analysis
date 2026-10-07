import ComputableAnalysis.ModularForms.PairedStripDerivativePrefixes
import ComputableAnalysis.ModularForms.PairedDerivativeInvariance

/-! Exact finite derivative-prefix agreement beneath the canonical derivative. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedFiniteMap_global_derivative_prefix (K : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((pairedFiniteMap_holomorphic K).derivative z hz).val.Equiv
      (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).val) 0 K) :=
  equiv_trans ((pairedFiniteMap_holomorphic K).derivative z hz).property
    (ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalDerivative z hz (n+1)).property) 0 K)
    (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) 0 K)
    (pairedFiniteMap_derivative K z hz)
    (ScalarSeries.block_congr _ _ (fun n => equiv_symm (pairedGlobalDerivativeTermMap_eval n z hz)) 0 K)

theorem pairedPartialFractionDerivative_prefix_tail (B : Nat) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (hroom : Small z.val ((B:Rat)-1)) :
    (pairedPartialFractionDerivative z hz).val.Equiv
      (add ((integerReciprocalMap_holomorphic 0).derivative z hz).val
        (add (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).val) 0 (4*B))
          (pairedDerivativeTailValue z hz B))) := by
  have hc := pairedPartialFractionDerivative_cutoff B z hz hroom
  have hB := pairedCutoff_room_small B z hroom
  exact equiv_trans (pairedPartialFractionDerivative z hz).property
    (pairedWholeJoinedDerivative B z ⟨hz,hB⟩).property
    (add_valid ((integerReciprocalMap_holomorphic 0).derivative z hz).property
      (add_valid (ScalarSeries.block_valid _
        (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) 0 (4*B))
        (pairedDerivativeTailValue_valid z hz B hB)))
    (equiv_symm hc)
    (add_equiv (equiv_refl _ ((integerReciprocalMap_holomorphic 0).derivative z hz).property)
      (add_equiv (pairedFiniteMap_global_derivative_prefix (4*B) z hz)
        (equiv_refl _ (pairedDerivativeTailValue_valid z hz B hB))))

end ComputableAnalysis.ModularForms
