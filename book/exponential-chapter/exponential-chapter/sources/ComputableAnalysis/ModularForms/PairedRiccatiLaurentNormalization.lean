import ComputableAnalysis.ModularForms.PairedRiccatiQuadraticCenter

/-! Exact center value and quantitative normalization on the punctured lattice chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedRiccatiExtension_center_identity (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (he : z.val.Equiv zero) :
    (pairedRiccatiExtension z hz).val.Equiv pairedRiccatiCenterConstant.val := by
  have ht := pairedRegularDivisionValue_at_zero z hz he
  exact equiv_trans (pairedRiccatiExtension z hz).property
    (add_valid (pairedRegularDivisionMap.eval z hz).property
      (add_valid (pairedRegularDivisionMap.eval z hz).property
        (pairedRegularDivisionMap.eval z hz).property))
    pairedRiccatiCenterConstant.property
    (pairedRiccatiExtension_at_zero z hz he)
    (add_equiv ht (add_equiv ht ht))

theorem pairedLaurent_riccati_center_bound (z : Scalar)
    (hz : pairedZeroLaurentMap.domain z) (R : Rat)
    (hR : 0 ≤ R) (hRq : R ≤ (1:Rat)/4) (hs : Small z.val R) :
    Small (sub (add (pairedZeroLaurentMap_holomorphic.derivative z hz).val
      (mul (pairedZeroLaurentMap.eval z hz).val (pairedZeroLaurentMap.eval z hz).val))
      pairedRiccatiCenterConstant.val) (25088*R*R) := by
  have hv := add_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property
    (mul_valid (pairedZeroLaurentMap.eval z hz).property
      (pairedZeroLaurentMap.eval z hz).property)
  exact Small.congr
    (sub_valid (pairedRiccatiExtension z hz.1).property pairedRiccatiCenterConstant.property)
    (sub_valid hv pairedRiccatiCenterConstant.property)
    (FunctionTheory.sub_congr (equiv_symm (pairedLaurent_riccati_extension z hz))
      (equiv_refl _ pairedRiccatiCenterConstant.property))
    (pairedRiccatiExtension_center_bound z hz.1 R hR hRq hs)

end ComputableAnalysis.ModularForms
