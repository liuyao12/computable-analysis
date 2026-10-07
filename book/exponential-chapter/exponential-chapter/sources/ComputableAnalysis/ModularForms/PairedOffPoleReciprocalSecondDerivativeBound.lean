import ComputableAnalysis.ModularForms.PairedRiccatiLocalKernelProductBound

/-! Actual second-derivative control for shifted reciprocals away from pole charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerReciprocalOffPoleDerivativeMap_derivative_outside_charts_bound
    (k : Int) (z : Scalar) (hz : (integerReciprocalOffPoleMap k).domain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    Small ((integerReciprocalOffPoleDerivativeMap_holomorphic k).derivative z hz).val 2097152 := by
  have hi := integerReciprocalOffPoleMap_outside_charts_bound k z hz hout
  have hd := integerReciprocalOffPoleMap_derivative_outside_charts_bound k z hz hout
  have hm := Small.mul ((integerReciprocalOffPoleMap_holomorphic k).derivative z hz).property
    ((integerReciprocalOffPoleMap k).eval z hz).property
    (show (0:Rat)≤8192 by decide +kernel) (show (0:Rat)≤64 by decide +kernel) hd hi
  have hn := Small.mul ((integerReciprocalOffPoleMap k).eval z hz).property
    ((integerReciprocalOffPoleMap_holomorphic k).derivative z hz).property
    (show (0:Rat)≤64 by decide +kernel) (show (0:Rat)≤8192 by decide +kernel) hi hd
  exact (SeriesLimitLaws.small_neg (LocalODE.small_add hm hn)).mono (by decide +kernel)

end ComputableAnalysis.ModularForms
