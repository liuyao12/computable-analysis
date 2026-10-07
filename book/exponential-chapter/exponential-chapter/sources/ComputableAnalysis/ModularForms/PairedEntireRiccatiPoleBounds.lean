import ComputableAnalysis.ModularForms.PairedEntireRiccati
import ComputableAnalysis.ModularForms.PairedRiccatiIntegerBounds

/-! Bounds on the entire Riccati map in every integer pole chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedEntireRiccatiMap_integer_bound (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z) :
    Small (pairedEntireRiccatiMap.eval z trivial).val 2208 :=
  Small.congr ((pairedIntegerRiccatiExtensionMap k).eval z hz).property
    (pairedEntireRiccatiMap.eval z trivial).property
    (pairedEntireRiccatiMap_chart_agreement (.pole k) z hz)
    (pairedIntegerRiccatiExtension_bound k z hz)

theorem pairedEntireRiccatiMap_integer_center_bound (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z)
    (R : Rat) (hR : 0≤R) (hRq : R≤(1:Rat)/4)
    (hs : Small (integerShiftScalar z (-k)).val R) :
    Small (sub (pairedEntireRiccatiMap.eval z trivial).val
      pairedRiccatiCenterConstant.val) (25088*R*R) :=
  Small.congr
    (sub_valid ((pairedIntegerRiccatiExtensionMap k).eval z hz).property
      pairedRiccatiCenterConstant.property)
    (sub_valid (pairedEntireRiccatiMap.eval z trivial).property
      pairedRiccatiCenterConstant.property)
    (FunctionTheory.sub_congr (pairedEntireRiccatiMap_chart_agreement (.pole k) z hz)
      (equiv_refl _ pairedRiccatiCenterConstant.property))
    (pairedIntegerRiccatiExtension_center_bound k z hz R hR hRq hs)

theorem pairedEntireRiccatiMap_derivative_at_integer (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z)
    (he : z.val.Equiv (rationalInteger k).val) :
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val.Equiv zero :=
  equiv_trans (pairedEntireRiccatiMap_holomorphic.derivative z trivial).property
    ((pairedIntegerRiccatiExtensionMap_holomorphic k).derivative z hz).property
    (ofQComplex_valid _)
    (equiv_symm (pairedEntireRiccatiMap_chart_derivative_agreement (.pole k) z hz))
    (pairedIntegerRiccatiExtension_derivative_at_integer k z hz he)

end ComputableAnalysis.ModularForms
