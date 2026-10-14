import ComputableAnalysis.ModularForms.RepresentedOutsideQuarterInverseBound
import ComputableAnalysis.ModularForms.PairedEntireRiccatiPoleBounds

/-! Uniform reciprocal control on the complement of all integer pole charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem outsideIntegerPoleCharts_shift_not_interior (z : Scalar)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) (k : Int) :
    ¬LocalODE.interior (1/4) (integerShiftScalar z k) := by
  intro h
  apply hout
  refine ⟨-k, trivial, ?_⟩
  change LocalODE.interior (1/4) (integerShiftScalar z (-(-k)))
  simpa only [Int.neg_neg] using h

theorem outsideIntegerPoleCharts_domain (z : Scalar)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) :
    pairedOffPoleDomain z := by
  rcases pairedRiccatiCharts_cover z with h | h
  · exact h
  · exact False.elim (hout h)

theorem globalIntegerReciprocal_outside_pole_charts_bound (z : Scalar)
    (hz : pairedOffPoleDomain z)
    (hout : ¬∃ j : Int, (pairedIntegerRiccatiExtensionMap j).domain z) (k : Int) :
    Small (globalOffPoleIntegerReciprocal z hz k).val 64 :=
  representedInverse_outside_quarter_bound (integerShiftScalar z k)
    (pairedOffPoleDomain_integer_nonzero z hz k)
    (outsideIntegerPoleCharts_shift_not_interior z hout k)

end ComputableAnalysis.ModularForms
