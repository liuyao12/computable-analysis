import ComputableAnalysis.ModularForms.PairedGlobalOffPoleHolomorphic

/-! Exact agreement of the global off-pole maps with the canonical upper-half-plane maps. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalOffPole_upper_mem (z : Scalar) (hz : InUpperHalfPlane z.val) : pairedOffPoleDomain z :=
  ⟨upperScalar_nonzero z hz,upperPairedSeriesDomain z hz⟩

theorem pairedGlobalOffPoleAssemblyMap_upper_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (upperPairedPartialFractionValue z hz) :=
  pairedOffPoleAssemblyMap_upper_agreement (pairedOffPoleCanonicalCutoff z) z hz
    (pairedOffPoleCanonicalCutoff_interior z)

theorem pairedGlobalOffPoleAssemblyMap_upper_derivative_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (pairedPartialFractionDerivative z hz).val :=
  pairedOffPoleAssemblyMap_upper_derivative_agreement (pairedOffPoleCanonicalCutoff z) z hz
    (pairedOffPoleCanonicalCutoff_interior z)

theorem pairedGlobalOffPoleAssemblyMap_upper_secondDerivative_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleAssemblyMap_derivative_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (pairedCanonicalSecondDerivative z hz).val :=
  pairedOffPoleAssemblyMap_upper_secondDerivative_agreement (pairedOffPoleCanonicalCutoff z) z hz
    (pairedOffPoleCanonicalCutoff_interior z)

theorem pairedGlobalOffPoleRiccatiMap_upper_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleRiccatiMap.eval z (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (pairedUpperRiccatiValue z hz).val := by
  have hp := pairedGlobalOffPoleAssemblyMap_upper_agreement z hz
  exact add_equiv (pairedGlobalOffPoleAssemblyMap_upper_derivative_agreement z hz)
    (mul_equiv (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).property
      (upperPairedPartialFractionValue_valid z hz)
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedGlobalOffPole_upper_mem z hz)).property
      (upperPairedPartialFractionValue_valid z hz) hp hp)

theorem pairedGlobalOffPoleRiccatiMap_upper_derivative_agreement (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)).val.Equiv
      (pairedUpperRiccatiDerivative z hz).val := by
  have he := pairedGlobalOffPoleRiccatiMap_holomorphic.derivative_equiv_on_overlap
    pairedUpperRiccatiMap_holomorphic
    (fun z _ hz => pairedGlobalOffPoleRiccatiMap_upper_agreement z hz)
    z (pairedGlobalOffPole_upper_mem z hz) hz
  exact equiv_trans
    (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)).property
    (pairedUpperRiccatiMap_holomorphic.derivative z hz).property (pairedUpperRiccatiDerivative z hz).property
    he (pairedUpperRiccatiMap_derivative z hz)

end ComputableAnalysis.ModularForms
