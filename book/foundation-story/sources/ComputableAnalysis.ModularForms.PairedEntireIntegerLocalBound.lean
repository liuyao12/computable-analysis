import ComputableAnalysis.ModularForms.PairedEntireIntegerNormalization

/-! Quantitative local normalization without caller-supplied pole charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedEntireRiccatiMap_near_integer_bound (k : Int) (z : Scalar)
    (R : Rat) (hR : 0≤R) (hRq : R<(1:Rat)/4)
    (hs : Small (integerShiftScalar z (-k)).val R) :
    Small (sub (pairedEntireRiccatiMap.eval z trivial).val
      pairedRiccatiCenterConstant.val) (25088*R*R) := by
  have hm : (pairedIntegerRiccatiExtensionMap k).domain z := ⟨trivial,R,hR,hRq,hs⟩
  exact pairedEntireRiccatiMap_integer_center_bound k z hm R hR (Rat.le_of_lt hRq) hs

end ComputableAnalysis.ModularForms
