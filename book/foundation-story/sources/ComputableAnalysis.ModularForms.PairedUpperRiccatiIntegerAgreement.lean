import ComputableAnalysis.ModularForms.PairedUpperRiccatiAgreement
import ComputableAnalysis.ModularForms.PairedDerivativeIntegerPeriodicity

/-! Canonical Riccati periodicity and agreement at every integer pole chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedUpperRiccatiValue_period_int (k : Int) (z : Scalar)
    (hu : InUpperHalfPlane z.val) :
    (pairedUpperRiccatiValue (integerShiftScalar z k) (integerShiftScalar_upper z hu k)).val.Equiv
      (pairedUpperRiccatiValue z hu).val := by
  have hp := upperPairedPartialFractionValue_period_int z hu k
  exact add_equiv (pairedPartialFractionDerivative_period_int k z hu)
    (mul_equiv (upperPairedPartialFractionValue_valid (integerShiftScalar z k) (integerShiftScalar_upper z hu k)) (upperPairedPartialFractionValue_valid z hu)
      (upperPairedPartialFractionValue_valid (integerShiftScalar z k) (integerShiftScalar_upper z hu k)) (upperPairedPartialFractionValue_valid z hu) hp hp)

theorem pairedUpperRiccati_integer_extension_agreement (k : Int) (z : Scalar)
    (hz : (pairedIntegerLaurentMap k).domain z) (hu : InUpperHalfPlane z.val) :
    (pairedUpperRiccatiValue z hu).val.Equiv
      ((pairedIntegerRiccatiExtensionMap k).eval z ⟨hz.1,hz.2.1⟩).val := by
  let w := integerShiftScalar z (-k)
  have hw := integerShiftScalar_upper z hu (-k)
  exact equiv_trans (pairedUpperRiccatiValue z hu).property
    (pairedUpperRiccatiValue w hw).property
    ((pairedIntegerRiccatiExtensionMap k).eval z ⟨hz.1,hz.2.1⟩).property
    (equiv_symm (pairedUpperRiccatiValue_period_int (-k) z hu))
    (pairedUpperRiccati_extension_agreement w (compose_outer_mem hz) hw)

end ComputableAnalysis.ModularForms
