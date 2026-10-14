import ComputableAnalysis.ModularForms.PairedGlobalReflectionDerivative
import ComputableAnalysis.ModularForms.PairedEntireUpperRiccatiBound

/-! Even reflection of the actual entire map, including all filled-in poles. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedIntegerRiccatiExtension_reflection_mem (j : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap j).domain z) :
    (pairedIntegerRiccatiExtensionMap (-j)).domain (pairedReflectionMap.eval z trivial) := by
  refine ⟨trivial,?_⟩
  have he := pairedReflection_shift_argument z j
  obtain ⟨r,hr,hrq,hs⟩ := compose_outer_mem hz
  have hb := Small.congr (neg_valid (integerShiftScalar z (-j)).property)
    (integerShiftScalar (pairedReflectionMap.eval z trivial) j).property
    (equiv_symm he) (SeriesLimitLaws.small_neg hs)
  change LocalODE.interior (1/4) (integerShiftScalar (pairedReflectionMap.eval z trivial) (-(-j)))
  simpa only [Int.neg_neg] using (show LocalODE.interior (1/4)
    (integerShiftScalar (pairedReflectionMap.eval z trivial) j) from ⟨r,hr,hrq,hb⟩)

theorem pairedIntegerRiccatiExtension_reflection (j : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap j).domain z) :
    ((pairedIntegerRiccatiExtensionMap (-j)).eval (pairedReflectionMap.eval z trivial)
      (pairedIntegerRiccatiExtension_reflection_mem j z hz)).val.Equiv
      ((pairedIntegerRiccatiExtensionMap j).eval z hz).val := by
  have hw := compose_outer_mem (pairedIntegerRiccatiExtension_reflection_mem j z hz)
  have he : (integerShiftScalar (pairedReflectionMap.eval z trivial) (-(-j))).val.Equiv
      (neg (integerShiftScalar z (-j)).val) := by
    simpa only [Int.neg_neg] using pairedReflection_shift_argument z j
  exact pairedRiccatiExtension_even _ _ (compose_outer_mem hz) hw he

theorem pairedEntireRiccatiMap_reflection (z : Scalar) :
    (pairedEntireRiccatiMap.eval (pairedReflectionMap.eval z trivial) trivial).val.Equiv
      (pairedEntireRiccatiMap.eval z trivial).val := by
  obtain hz | ⟨j,hz⟩ := pairedRiccatiCharts_cover z
  · have hw := pairedOffPoleDomain_reflection z hz
    exact equiv_trans (pairedEntireRiccatiMap.eval (pairedReflectionMap.eval z trivial) trivial).property
      (pairedGlobalOffPoleRiccatiMap.eval (pairedReflectionMap.eval z trivial) hw).property
      (pairedEntireRiccatiMap.eval z trivial).property
      (equiv_symm (pairedEntireRiccatiMap_chart_agreement .offPole _ hw))
      (equiv_trans (pairedGlobalOffPoleRiccatiMap.eval (pairedReflectionMap.eval z trivial) hw).property
        (pairedGlobalOffPoleRiccatiMap.eval z hz).property (pairedEntireRiccatiMap.eval z trivial).property
        (pairedGlobalOffPoleRiccatiMap_reflection z hz) (pairedEntireRiccatiMap_chart_agreement .offPole z hz))
  · have hw := pairedIntegerRiccatiExtension_reflection_mem j z hz
    exact equiv_trans (pairedEntireRiccatiMap.eval (pairedReflectionMap.eval z trivial) trivial).property
      ((pairedIntegerRiccatiExtensionMap (-j)).eval (pairedReflectionMap.eval z trivial) hw).property
      (pairedEntireRiccatiMap.eval z trivial).property
      (equiv_symm (pairedEntireRiccatiMap_chart_agreement (.pole (-j)) _ hw))
      (equiv_trans ((pairedIntegerRiccatiExtensionMap (-j)).eval (pairedReflectionMap.eval z trivial) hw).property
        ((pairedIntegerRiccatiExtensionMap j).eval z hz).property (pairedEntireRiccatiMap.eval z trivial).property
        (pairedIntegerRiccatiExtension_reflection j z hz) (pairedEntireRiccatiMap_chart_agreement (.pole j) z hz))

end ComputableAnalysis.ModularForms
