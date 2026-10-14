import ComputableAnalysis.ModularForms.PairedGlobalFirstDerivativeHolomorphic
import ComputableAnalysis.ModularForms.PairedUpperRiccatiIntegerHolomorphic

/-! Holomorphicity of the actual canonical Riccati expression on the whole upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

noncomputable def pairedUpperRiccatiMap_holomorphic : Holomorphic pairedUpperRiccatiMap := by
  let hp := pairedPartialFractionMap_holomorphic.productOn pairedPartialFractionMap_holomorphic
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
  let hf := pairedCanonicalFirstDerivativeMap_holomorphic.sumOn hp
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
  apply hf.transfer pairedUpperRiccatiMap (fun _ hz => hz) ⟨upperRadius,upperRadius_inside⟩
  intro z hz
  exact equiv_refl _ (pairedUpperRiccatiValue z hz).property

end ComputableAnalysis.ModularForms
