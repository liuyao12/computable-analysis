import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTail

/-! Actual finite-plus-tail second-derivative candidates including the central reciprocal. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedGlobalSecondDerivativeAssembly (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) : Scalar :=
  scalarSum (integerReciprocalSecondDerivative 0 z hz)
    ⟨add (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm n z hz).val) 0 (4*B))
      (pairedGlobalSecondDerivativeTailValue z hz B),
      add_valid (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTerm n z hz).property) 0 (4*B))
        (pairedGlobalSecondDerivativeTailValue_valid z hz B hB)⟩

def pairedGlobalSecondDerivativeAssemblyPrefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B N : Nat) : Scalar :=
  scalarSum (integerReciprocalSecondDerivative 0 z hz)
    ⟨add (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm n z hz).val) 0 (4*B))
      (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).val) 0 (N+1)),
      add_valid (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTerm n z hz).property) 0 (4*B))
        (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).property) 0 (N+1))⟩

theorem pairedGlobalSecondDerivativeAssembly_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedGlobalSecondDerivativeAssembly z hz B hB).val
      (pairedGlobalSecondDerivativeAssemblyPrefix z hz B N).val) (65536*((N+1:Nat):Rat)⁻¹) := by
  have he : (sub (pairedGlobalSecondDerivativeTailValue z hz B)
      (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).val) 0 (N+1))).Equiv
      (sub (pairedGlobalSecondDerivativeAssembly z hz B hB).val
        (pairedGlobalSecondDerivativeAssemblyPrefix z hz B N).val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedGlobalSecondDerivativeTailValue_valid z hz B hB)
        (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).property) 0 (N+1)))
      (hright := sub_valid (pairedGlobalSecondDerivativeAssembly z hz B hB).property
        (pairedGlobalSecondDerivativeAssemblyPrefix z hz B N).property)
    let C := ComplexRawQuotient.ofRaw (integerReciprocalSecondDerivative 0 z hz).val
      (integerReciprocalSecondDerivative 0 z hz).property
    let F := ComplexRawQuotient.ofRaw
      (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm n z hz).val) 0 (4*B))
      (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTerm n z hz).property) 0 (4*B))
    let T := ComplexRawQuotient.ofRaw (pairedGlobalSecondDerivativeTailValue z hz B)
      (pairedGlobalSecondDerivativeTailValue_valid z hz B hB)
    let P := ComplexRawQuotient.ofRaw
      (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).val) 0 (N+1))
      (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).property) 0 (N+1))
    change T-P=(C+(F+T))-(C+(F+P))
    grind only
  exact Small.congr
    (sub_valid (pairedGlobalSecondDerivativeTailValue_valid z hz B hB)
      (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTailTerm z hz B n).property) 0 (N+1)))
    (sub_valid (pairedGlobalSecondDerivativeAssembly z hz B hB).property
      (pairedGlobalSecondDerivativeAssemblyPrefix z hz B N).property) he
    (pairedGlobalSecondDerivativeTailValue_close z hz B hB N)

end ComputableAnalysis.ModularForms
