import ComputableAnalysis.ModularForms.PairedEntireGlobalBound

/-! Exact normalization of the entire Riccati map at represented integers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedIntegerRiccatiExtension_at_integer_mem (k : Int) (z : Scalar)
    (he : z.val.Equiv (rationalInteger k).val) :
    (pairedIntegerRiccatiExtensionMap k).domain z := by
  have hs : Small (integerShiftScalar z (-k)).val 0 :=
    Small.congr (ofQComplex_valid _) (integerShiftScalar z (-k)).property
      (equiv_symm (integerShiftScalar_at_integer k z he))
      (Small.zero (by decide +kernel))
  exact ⟨trivial,0,by decide +kernel,by decide +kernel,hs⟩

theorem pairedEntireRiccatiMap_value_at_integer (k : Int) (z : Scalar)
    (he : z.val.Equiv (rationalInteger k).val) :
    (pairedEntireRiccatiMap.eval z trivial).val.Equiv pairedRiccatiCenterConstant.val := by
  have hz := pairedIntegerRiccatiExtension_at_integer_mem k z he
  have hc := pairedRiccatiExtension_center_identity (integerShiftScalar z (-k))
    (compose_outer_mem hz) (integerShiftScalar_at_integer k z he)
  exact equiv_trans (pairedEntireRiccatiMap.eval z trivial).property
    ((pairedIntegerRiccatiExtensionMap k).eval z hz).property
    pairedRiccatiCenterConstant.property
    (equiv_symm (pairedEntireRiccatiMap_chart_agreement (.pole k) z hz)) hc

theorem pairedEntireRiccatiMap_derivative_at_integer_exact (k : Int) (z : Scalar)
    (he : z.val.Equiv (rationalInteger k).val) :
    (pairedEntireRiccatiMap_holomorphic.derivative z trivial).val.Equiv zero :=
  pairedEntireRiccatiMap_derivative_at_integer k z
    (pairedIntegerRiccatiExtension_at_integer_mem k z he) he

end ComputableAnalysis.ModularForms
