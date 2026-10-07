import ComputableAnalysis.ModularForms.PairedOffPoleFiniteSecondDerivativeBound

/-! Quantitative derivative control of the actual off-pole Riccati map. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleRiccatiMap_three_derivative_outside_charts_bound
    (z : Scalar) (hz : (pairedOffPoleRiccatiMap 3).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((pairedOffPoleRiccatiMap_holomorphic 3).derivative z hz).val 1427432192 := by
  have hv := pairedOffPoleAssemblyMap_three_outside_charts_bound z hz hout
  have hd : Small ((pairedOffPoleAssemblyMap_holomorphic 3).derivative z hz).val 214032 :=
    (pairedOffPoleAssemblyMap_derivative_outside_charts_bound 3 z hz hout).mono (by decide +kernel)
  have hs : Small ((pairedOffPoleAssemblyMap_derivative_holomorphic 3).derivative z hz).val 54202880 :=
    (pairedOffPoleAssemblyMap_second_derivative_outside_charts_bound 3 z hz hout).mono (by decide +kernel)
  have hp := Small.mul ((pairedOffPoleAssemblyMap_holomorphic 3).derivative z hz).property
    ((pairedOffPoleAssemblyMap 3).eval z hz).property
    (show (0:Rat)≤214032 by decide +kernel) (show (0:Rat)≤1604 by decide +kernel) hd hv
  have hq := Small.mul ((pairedOffPoleAssemblyMap 3).eval z hz).property
    ((pairedOffPoleAssemblyMap_holomorphic 3).derivative z hz).property
    (show (0:Rat)≤1604 by decide +kernel) (show (0:Rat)≤214032 by decide +kernel) hv hd
  exact (LocalODE.small_add hs (LocalODE.small_add hp hq)).mono (by decide +kernel)

theorem pairedEntireRiccatiMap_fixed_box_derivative_outside_charts_bound
    (z : Scalar) (hs : Small z.val 2)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val 1427432192 := by
  have hd := outsideIntegerPoleCharts_domain z hout
  have hi : LocalODE.interior (3:Rat) z := ⟨2,by decide +kernel,by decide +kernel,hs⟩
  have hm := pairedOffPoleAssemblyMap_global_mem 3 z hd hi
  have hb := pairedOffPoleRiccatiMap_three_derivative_outside_charts_bound z hm hout
  have he := equiv_trans ((pairedOffPoleRiccatiMap_holomorphic 3).derivative z hm).property
    (pairedGlobalOffPoleRiccatiMap_holomorphic.derivative z hd).property
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property
    (pairedGlobalOffPoleRiccatiMap_chart_derivative_agreement 3 z hm)
    (pairedEntireRiccatiMap_chart_derivative_agreement .offPole z hd)
  exact Small.congr ((pairedOffPoleRiccatiMap_holomorphic 3).derivative z hm).property
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property he hb

end ComputableAnalysis.ModularForms
