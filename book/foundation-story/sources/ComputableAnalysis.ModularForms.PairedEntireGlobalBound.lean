import ComputableAnalysis.ModularForms.PairedEntireFixedBoxBound
import ComputableAnalysis.ModularForms.RepresentedOrderTotal

/-! A whole-plane bound for the actual entire paired Riccati function. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedEntireRiccatiMap_global_bound (z : Scalar) :
    Small (pairedEntireRiccatiMap.eval z trivial).val 5369840 := by
  rcases representedReal_le_total z.val.imagPart (RealRaw.ofRat (-2))
    (imagPart_valid z.property) (RealRaw.ofRat_valid _) with hlo | hlo
  · exact (pairedEntireRiccatiMap_below_minus_two_bound z hlo).mono (by decide +kernel)
  · rcases representedReal_le_total z.val.imagPart (RealRaw.ofRat 2)
      (imagPart_valid z.property) (RealRaw.ofRat_valid _) with hup | hup
    · exact pairedEntireRiccatiMap_middle_band_bound z hlo hup
    · exact (pairedEntireRiccatiMap_above_two_bound_exact z hup).mono (by decide +kernel)

end ComputableAnalysis.ModularForms
