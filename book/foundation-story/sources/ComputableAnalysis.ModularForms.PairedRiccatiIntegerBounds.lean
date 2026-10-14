import ComputableAnalysis.ModularForms.PairedRiccatiExtensionDerivativeCenter
import ComputableAnalysis.ModularForms.PairedUpperRiccatiIntegerAgreement
import ComputableAnalysis.ModularForms.PairedRiccatiExtensionBound

/-! Uniform bounds for actual Riccati values on all integer pole charts. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedIntegerRiccatiExtension_bound (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z) :
    Small ((pairedIntegerRiccatiExtensionMap k).eval z hz).val 2208 :=
  pairedRiccatiExtension_bound (integerShiftScalar z (-k)) (compose_outer_mem hz)

theorem pairedUpperRiccatiValue_integer_bound (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z)
    (hu : InUpperHalfPlane z.val) :
    Small (pairedUpperRiccatiValue z hu).val 2208 := by
  have hp : (pairedIntegerLaurentMap k).domain z :=
    ⟨hz.1,hz.2,upperScalar_nonzero (integerShiftScalar z (-k))
      (integerShiftScalar_upper z hu (-k))⟩
  exact Small.congr ((pairedIntegerRiccatiExtensionMap k).eval z hz).property
    (pairedUpperRiccatiValue z hu).property
    (equiv_symm (pairedUpperRiccati_integer_extension_agreement k z hp hu))
    (pairedIntegerRiccatiExtension_bound k z hz)

theorem pairedUpperRiccatiValue_integer_center_bound (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z)
    (hu : InUpperHalfPlane z.val) (R : Rat) (hR : 0≤R) (hRq : R≤(1:Rat)/4)
    (hs : Small (integerShiftScalar z (-k)).val R) :
    Small (sub (pairedUpperRiccatiValue z hu).val pairedRiccatiCenterConstant.val)
      (25088*R*R) := by
  have hp : (pairedIntegerLaurentMap k).domain z :=
    ⟨hz.1,hz.2,upperScalar_nonzero (integerShiftScalar z (-k))
      (integerShiftScalar_upper z hu (-k))⟩
  exact Small.congr
    (sub_valid ((pairedIntegerRiccatiExtensionMap k).eval z hz).property pairedRiccatiCenterConstant.property)
    (sub_valid (pairedUpperRiccatiValue z hu).property pairedRiccatiCenterConstant.property)
    (FunctionTheory.sub_congr
      (equiv_symm (pairedUpperRiccati_integer_extension_agreement k z hp hu))
      (equiv_refl _ pairedRiccatiCenterConstant.property))
    (pairedIntegerRiccatiExtension_center_bound k z hz R hR hRq hs)

end ComputableAnalysis.ModularForms
