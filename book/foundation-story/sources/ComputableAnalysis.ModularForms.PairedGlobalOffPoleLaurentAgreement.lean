import ComputableAnalysis.ModularForms.PairedGlobalOffPoleUpperAgreement

/-! Exact Laurent and Riccati agreement on the full punctured disk, across the real axis. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalOffPoleAssemblyMap_canonicalValue (z : Scalar) (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleAssemblyMap.eval z hz).val.Equiv
      (pairedPartialFractionValue z hz.1 hz.2) := by
  let B := pairedOffPoleCanonicalCutoff z
  let hB := pairedOffPoleCanonicalCutoff_mem z hz
  have hi := RepresentedReciprocal.inverse_congr (integerShiftScalar z 0) z hB.1.2 hz.1
    (integerShiftScalar_zero_equiv z)
  have hf := add_equiv (pairedFiniteOffPoleMap_full_agreement (4*B) z hB.2.1 hz.2)
    (equiv_refl _ ((pairedOffPoleTailMap B).eval z hB.2.2).property)
  have hs := equiv_trans
    (add_valid ((pairedFiniteOffPoleMap (4*B)).eval z hB.2.1).property
      ((pairedOffPoleTailMap B).eval z hB.2.2).property)
    (pairedFullValue_valid z hz.2 B (LocalODE.interior_bound _ z hB.2.2))
    (pairedSeriesValue_valid z hz.2) hf
    (equiv_symm (pairedSeriesValue_agrees z hz.2 B (LocalODE.interior_bound _ z hB.2.2)))
  exact add_equiv hi hs

theorem pairedZeroLaurentMap_global_mem (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    pairedOffPoleDomain z :=
  ⟨hz.2,pairedSmallDisk_domain z (1/4) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ z hz.1)⟩

theorem pairedZeroLaurentMap_global_agreement (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    (pairedZeroLaurentMap.eval z hz).val.Equiv
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedZeroLaurentMap_global_mem z hz)).val :=
  equiv_symm (pairedGlobalOffPoleAssemblyMap_canonicalValue z (pairedZeroLaurentMap_global_mem z hz))

theorem pairedZeroLaurentMap_global_derivative_agreement (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    (pairedZeroLaurentMap_holomorphic.derivative z hz).val.Equiv
      (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedZeroLaurentMap_global_mem z hz)).val :=
  pairedZeroLaurentMap_holomorphic.derivative_equiv_on_overlap pairedGlobalOffPoleAssemblyMap_holomorphic
    (fun z hz _ => pairedZeroLaurentMap_global_agreement z hz)
    z hz (pairedZeroLaurentMap_global_mem z hz)

theorem pairedGlobalOffPoleRiccatiMap_zero_extension_agreement (z : Scalar)
    (hz : pairedZeroLaurentMap.domain z) :
    (pairedGlobalOffPoleRiccatiMap.eval z (pairedZeroLaurentMap_global_mem z hz)).val.Equiv
      (pairedRiccatiExtension z hz.1).val := by
  have hp := pairedZeroLaurentMap_global_agreement z hz
  have hd := pairedZeroLaurentMap_global_derivative_agreement z hz
  have he := add_equiv (equiv_symm hd)
    (mul_equiv
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedZeroLaurentMap_global_mem z hz)).property
      (pairedZeroLaurentMap.eval z hz).property
      (pairedGlobalOffPoleAssemblyMap.eval z (pairedZeroLaurentMap_global_mem z hz)).property
      (pairedZeroLaurentMap.eval z hz).property (equiv_symm hp) (equiv_symm hp))
  exact equiv_trans (pairedGlobalOffPoleRiccatiMap.eval z (pairedZeroLaurentMap_global_mem z hz)).property
    (add_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property
      (mul_valid (pairedZeroLaurentMap.eval z hz).property (pairedZeroLaurentMap.eval z hz).property))
    (pairedRiccatiExtension z hz.1).property he (pairedLaurent_riccati_extension z hz)

theorem pairedGlobalOffPoleRiccatiMap_zero_extension_derivative_agreement (z : Scalar)
    (hz : pairedZeroLaurentMap.domain z) :
    (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative z (pairedZeroLaurentMap_global_mem z hz)).val.Equiv
      (pairedRiccatiExtensionMap_holomorphic.derivative z hz.1).val :=
  pairedGlobalOffPoleRiccatiMap_holomorphic.derivative_equiv_on_overlap pairedRiccatiExtensionMap_holomorphic
    (fun z hg he => pairedGlobalOffPoleRiccatiMap_zero_extension_agreement z ⟨he,hg.1⟩)
    z (pairedZeroLaurentMap_global_mem z hz) hz.1

end ComputableAnalysis.ModularForms
