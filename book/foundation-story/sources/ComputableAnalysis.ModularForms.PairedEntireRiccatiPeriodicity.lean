import ComputableAnalysis.ModularForms.PairedEntireRiccatiPoleBounds

/-! Integer periodicity of the actual entire Riccati map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerPoleChart_shift_argument (j k : Int) (z : Scalar) :
    (integerShiftScalar (integerShiftScalar z k) (-(j+k))).val.Equiv
      (integerShiftScalar z (-j)).val := by
  have h := integerShiftScalar_composition z k (-(j+k))
  simpa only [show k + -(j+k) = -j by omega] using h

theorem pairedIntegerRiccatiExtensionMap_shift_mem (j k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap j).domain z) :
    (pairedIntegerRiccatiExtensionMap (j+k)).domain (integerShiftScalar z k) := by
  refine ⟨trivial,?_⟩
  exact (pairedRiccatiExtensionMap.domain_congr _ _
    (integerPoleChart_shift_argument j k z)).mpr (compose_outer_mem hz)

theorem pairedIntegerRiccatiExtensionMap_shift_agreement (j k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap j).domain z) :
    ((pairedIntegerRiccatiExtensionMap (j+k)).eval (integerShiftScalar z k)
      (pairedIntegerRiccatiExtensionMap_shift_mem j k z hz)).val.Equiv
      ((pairedIntegerRiccatiExtensionMap j).eval z hz).val :=
  pairedRiccatiExtensionMap.eval_congr _ _ _ _ (integerPoleChart_shift_argument j k z)

theorem pairedEntireRiccatiMap_period_int (k : Int) (z : Scalar) :
    (pairedEntireRiccatiMap.eval (integerShiftScalar z k) trivial).val.Equiv
      (pairedEntireRiccatiMap.eval z trivial).val := by
  obtain hz | ⟨j,hz⟩ := pairedRiccatiCharts_cover z
  · have hw := pairedOffPoleDomain_shift z hz k
    exact equiv_trans (pairedEntireRiccatiMap.eval (integerShiftScalar z k) trivial).property
      (pairedGlobalOffPoleRiccatiMap.eval (integerShiftScalar z k) hw).property
      (pairedEntireRiccatiMap.eval z trivial).property
      (equiv_symm (pairedEntireRiccatiMap_chart_agreement .offPole _ hw))
      (equiv_trans (pairedGlobalOffPoleRiccatiMap.eval (integerShiftScalar z k) hw).property
        (pairedGlobalOffPoleRiccatiMap.eval z hz).property
        (pairedEntireRiccatiMap.eval z trivial).property
        (pairedGlobalOffPoleRiccatiMap_period_int k z hz)
        (pairedEntireRiccatiMap_chart_agreement .offPole z hz))
  · have hw := pairedIntegerRiccatiExtensionMap_shift_mem j k z hz
    exact equiv_trans (pairedEntireRiccatiMap.eval (integerShiftScalar z k) trivial).property
      ((pairedIntegerRiccatiExtensionMap (j+k)).eval (integerShiftScalar z k) hw).property
      (pairedEntireRiccatiMap.eval z trivial).property
      (equiv_symm (pairedEntireRiccatiMap_chart_agreement (.pole (j+k)) _ hw))
      (equiv_trans ((pairedIntegerRiccatiExtensionMap (j+k)).eval (integerShiftScalar z k) hw).property
        ((pairedIntegerRiccatiExtensionMap j).eval z hz).property
        (pairedEntireRiccatiMap.eval z trivial).property
        (pairedIntegerRiccatiExtensionMap_shift_agreement j k z hz)
        (pairedEntireRiccatiMap_chart_agreement (.pole j) z hz))

theorem pairedEntireRiccatiMap_derivative_period_int (k : Int) (z : Scalar) :
    (pairedEntireRiccatiMap_holomorphic.derivative (integerShiftScalar z k) trivial).val.Equiv
      (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val :=
  holomorphic_integer_translation_derivative pairedEntireRiccatiMap_holomorphic k
    (fun _ _ => trivial) (fun z _ => pairedEntireRiccatiMap_period_int k z) z trivial

end ComputableAnalysis.ModularForms
