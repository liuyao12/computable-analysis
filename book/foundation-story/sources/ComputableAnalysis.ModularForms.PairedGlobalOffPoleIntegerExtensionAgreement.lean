import ComputableAnalysis.ModularForms.PairedGlobalOffPoleDerivativePeriodicity

/-! Global Riccati agreement with every actual integer-pole extension across the real axis. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalOffPoleRiccatiMap_integer_extension_agreement (k : Int) (z : Scalar)
    (hz : pairedOffPoleDomain z) (hc : (pairedIntegerRiccatiExtensionMap k).domain z) :
    (pairedGlobalOffPoleRiccatiMap.eval z hz).val.Equiv
      ((pairedIntegerRiccatiExtensionMap k).eval z hc).val := by
  let w := integerShiftScalar z (-k)
  let hw := pairedOffPoleDomain_shift z hz (-k)
  let hq : pairedZeroLaurentMap.domain w := ⟨compose_outer_mem hc,hw.1⟩
  exact equiv_trans (pairedGlobalOffPoleRiccatiMap.eval z hz).property
    (pairedGlobalOffPoleRiccatiMap.eval w hw).property
    ((pairedIntegerRiccatiExtensionMap k).eval z hc).property
    (equiv_symm (pairedGlobalOffPoleRiccatiMap_period_int (-k) z hz))
    (pairedGlobalOffPoleRiccatiMap_zero_extension_agreement w hq)

theorem pairedGlobalOffPoleRiccatiMap_integer_extension_derivative_agreement (k : Int) (z : Scalar)
    (hz : pairedOffPoleDomain z) (hc : (pairedIntegerRiccatiExtensionMap k).domain z) :
    (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative z hz).val.Equiv
      ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hc).val :=
  pairedGlobalOffPoleRiccatiMap_holomorphic.derivative_equiv_on_overlap
    (pairedIntegerRiccatiExtensionMap_holomorphic k)
    (fun z hz hc => pairedGlobalOffPoleRiccatiMap_integer_extension_agreement k z hz hc) z hz hc

end ComputableAnalysis.ModularForms
