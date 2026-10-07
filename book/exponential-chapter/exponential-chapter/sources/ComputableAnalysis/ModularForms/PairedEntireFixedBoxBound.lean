import ComputableAnalysis.ModularForms.PairedOffPoleAssemblyDerivativeBound
import ComputableAnalysis.ModularForms.PairedMiddleBandReduction

/-! A proved bound for the entire Riccati map on a fixed represented box. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedEntireRiccatiMap_fixed_box_bound (z : Scalar) (hs : Small z.val 2) :
    Small (pairedEntireRiccatiMap.eval z trivial).val 5369840 := by
  classical
  by_cases hp : ∃ k : Int, (pairedIntegerRiccatiExtensionMap k).domain z
  · obtain ⟨k,hk⟩ := hp
    exact (pairedEntireRiccatiMap_integer_bound k z hk).mono (by decide +kernel)
  · have hd := outsideIntegerPoleCharts_domain z hp
    have hi : LocalODE.interior (3:Rat) z :=
      ⟨2,by decide +kernel,by decide +kernel,hs⟩
    have hm := pairedOffPoleAssemblyMap_global_mem 3 z hd hi
    have hb := pairedOffPoleRiccatiMap_three_outside_charts_bound z hm hp
    have he := equiv_trans ((pairedOffPoleRiccatiMap 3).eval z hm).property
      (pairedGlobalOffPoleRiccatiMap.eval z hd).property
      (pairedEntireRiccatiMap.eval z trivial).property
      (pairedGlobalOffPoleRiccatiMap_chart_agreement 3 z hm)
      (pairedEntireRiccatiMap_chart_agreement .offPole z hd)
    exact Small.congr ((pairedOffPoleRiccatiMap 3).eval z hm).property
      (pairedEntireRiccatiMap.eval z trivial).property he hb

theorem pairedEntireRiccatiMap_middle_band_bound (z : Scalar)
    (hlo : RealRaw.Le (RealRaw.ofRat (-2)) z.val.imagPart)
    (hup : RealRaw.Le z.val.imagPart (RealRaw.ofRat 2)) :
    Small (pairedEntireRiccatiMap.eval z trivial).val 5369840 :=
  pairedEntireRiccatiMap_middle_bound_of_small_bound 5369840
    pairedEntireRiccatiMap_fixed_box_bound z hlo hup

end ComputableAnalysis.ModularForms
