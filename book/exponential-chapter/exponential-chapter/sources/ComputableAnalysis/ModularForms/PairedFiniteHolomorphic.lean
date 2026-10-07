import ComputableAnalysis.ModularForms.PairedTailDerivative

/-! Holomorphic finite initial sums and their exact represented derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedFiniteMap (N : Nat) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨ScalarSeries.block (fun n => ((pairedReciprocalTermMap n).eval z hz).val) 0 N,
    ScalarSeries.block_valid _ (fun n => ((pairedReciprocalTermMap n).eval z hz).property) 0 N⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := ScalarSeries.block_congr _ _
    (fun n => (pairedReciprocalTermMap n).eval_congr z w hz hw he) 0 N

def pairedFiniteMap_holomorphic (N : Nat) : DomainFunctions.Holomorphic (pairedFiniteMap N) := by
  induction N with
  | zero =>
    apply (constantOn_holomorphic upperOpenData ⟨zero,ofQComplex_valid _⟩).transfer
      (pairedFiniteMap 0) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    have h := ih.sumOn (pairedReciprocalTermMap_holomorphic N)
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
    apply h.transfer (pairedFiniteMap (N+1)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    simp only [sumOn,pairedFiniteMap,scalarSum,ScalarSeries.block.eq_2,Nat.zero_add]
    exact equiv_refl _ (add_valid
      (ScalarSeries.block_valid _ (fun n => ((pairedReciprocalTermMap n).eval z hz).property) 0 N)
      ((pairedReciprocalTermMap N).eval z hz).property)

theorem pairedFiniteMap_eval (N : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedFiniteMap N).eval z hz).val.Equiv (upperPairedLatticePrefix z hz N) :=
  ScalarSeries.block_congr _ _ (fun n => pairedReciprocalTermMap_eval_agreement n z hz) 0 N

theorem pairedFiniteMap_derivative (N : Nat) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ((pairedFiniteMap_holomorphic N).derivative z hz).val.Equiv
      (ScalarSeries.block (fun n => (upperPairedReciprocalDerivative z hz (n+1)).val) 0 N) := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    simp only [ScalarSeries.block.eq_2,Nat.zero_add]
    exact add_equiv ih (pairedReciprocalTermMap_derivative N z hz)

end ComputableAnalysis.ModularForms
