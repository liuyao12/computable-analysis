import ComputableAnalysis.ModularForms.PairedIntegerRiccatiExtension

/-! Agreement of the canonical upper-half-plane Riccati expression with the actual extension. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedUpperRiccatiValue (z : Scalar) (hu : InUpperHalfPlane z.val) : Scalar :=
  let p : Scalar := ⟨upperPairedPartialFractionValue z hu,upperPairedPartialFractionValue_valid z hu⟩
  scalarSum (pairedPartialFractionDerivative z hu) (DomainFunctions.scalarProduct p p)

theorem pairedUpperRiccatiValue_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (he : z.val.Equiv w.val) :
    (pairedUpperRiccatiValue z hz).val.Equiv (pairedUpperRiccatiValue w hw).val := by
  have hp := pairedPartialFractionMap.eval_congr z w hz hw he
  exact add_equiv (pairedPartialFractionMap_holomorphic.derivative_congr z w hz hw he)
    (mul_equiv (upperPairedPartialFractionValue_valid z hz) (upperPairedPartialFractionValue_valid w hw)
      (upperPairedPartialFractionValue_valid z hz) (upperPairedPartialFractionValue_valid w hw) hp hp)

theorem pairedUpperRiccati_extension_agreement (z : Scalar)
    (hz : pairedZeroLaurentMap.domain z) (hu : InUpperHalfPlane z.val) :
    (pairedUpperRiccatiValue z hu).val.Equiv (pairedRiccatiExtension z hz.1).val := by
  have hp := pairedZeroLaurentMap_upper z hz hu
  have hd := pairedLaurentDerivative_upper_agreement z hz hu
  have he := add_equiv (equiv_symm hd)
    (mul_equiv (upperPairedPartialFractionValue_valid z hu) (pairedZeroLaurentMap.eval z hz).property
      (upperPairedPartialFractionValue_valid z hu) (pairedZeroLaurentMap.eval z hz).property
      (equiv_symm hp) (equiv_symm hp))
  exact equiv_trans (pairedUpperRiccatiValue z hu).property
    (add_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property
      (mul_valid (pairedZeroLaurentMap.eval z hz).property (pairedZeroLaurentMap.eval z hz).property))
    (pairedRiccatiExtension z hz.1).property he (pairedLaurent_riccati_extension z hz)

def pairedUpperRiccatiMap : DomainFunctions.Map where
  domain := InUpperHalfPlane ∘ Subtype.val
  eval := pairedUpperRiccatiValue
  domain_congr := pairedPartialFractionMap.domain_congr
  eval_congr := pairedUpperRiccatiValue_congr

def pairedUpperRiccatiLocalMap : DomainFunctions.Map :=
  onDomain pairedUpperRiccatiMap pairedLaurentUpperOpenData.invariant (fun _ hz => hz.1)

def pairedUpperRiccatiLocalMap_holomorphic : Holomorphic pairedUpperRiccatiLocalMap :=
  pairedRiccatiExtensionMap_holomorphic.transfer pairedUpperRiccatiLocalMap
    (fun _ hz => hz.2.1)
    ⟨pairedLaurentUpperOpenData.radius,pairedLaurentUpperOpenData.inside⟩
    (fun z hz => equiv_symm (pairedUpperRiccati_extension_agreement z hz.2 hz.1))

end ComputableAnalysis.ModularForms
