import ComputableAnalysis.ModularForms.PairedSeriesHolomorphic
import ComputableAnalysis.ModularForms.PairedIntegerPeriodicity

/-! Periodicity of the actual derivative follows from the actual series identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def integerTranslatedPairedHolomorphic (k : Int) : DomainFunctions.Holomorphic pairedPartialFractionMap := by
  have h := pairedPartialFractionMap_holomorphic.compose (integerAffineMap_holomorphic 1 k)
  apply h.transfer pairedPartialFractionMap
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) =>
      ⟨hz,integerShiftScalar_upper z hz k⟩) ⟨upperRadius,upperRadius_inside⟩
  intro z hz
  exact upperPairedPartialFractionValue_period_int z hz k

theorem pairedPartialFractionDerivative_period_int (k : Int) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedPartialFractionDerivative (integerShiftScalar z k) (integerShiftScalar_upper z hz k)).val.Equiv
      (pairedPartialFractionDerivative z hz).val := by
  have hi := (integerTranslatedPairedHolomorphic k).derivative_unique pairedPartialFractionMap_holomorphic z hz
  have hd : ((integerTranslatedPairedHolomorphic k).derivative z hz).val.Equiv
      (pairedPartialFractionDerivative (integerShiftScalar z k) (integerShiftScalar_upper z hz k)).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((integerTranslatedPairedHolomorphic k).derivative z hz).property)
      (hright := (pairedPartialFractionDerivative (integerShiftScalar z k)
        (integerShiftScalar_upper z hz k)).property)
    let X := ComplexRawQuotient.ofRaw
      (pairedPartialFractionDerivative (integerShiftScalar z k) (integerShiftScalar_upper z hz k)).val
      (pairedPartialFractionDerivative (integerShiftScalar z k) (integerShiftScalar_upper z hz k)).property
    change X*ComplexRawQuotient.ofQComplex ⟨((1:Int):Rat),0⟩=X
    rw [integer_constant]
    grind only
  exact equiv_trans (pairedPartialFractionDerivative (integerShiftScalar z k)
    (integerShiftScalar_upper z hz k)).property ((integerTranslatedPairedHolomorphic k).derivative z hz).property
    (pairedPartialFractionDerivative z hz).property (equiv_symm hd) hi

end ComputableAnalysis.ModularForms
