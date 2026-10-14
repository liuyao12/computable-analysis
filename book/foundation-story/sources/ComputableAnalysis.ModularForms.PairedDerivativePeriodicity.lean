import ComputableAnalysis.ModularForms.PairedSeriesHolomorphic
import ComputableAnalysis.ModularForms.PairedSeriesPeriodicity

/-! Periodicity of the actual derivative follows from the actual series identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def translatedPairedHolomorphic : DomainFunctions.Holomorphic pairedPartialFractionMap := by
  have h := pairedPartialFractionMap_holomorphic.compose (integerAffineMap_holomorphic 1 1)
  apply h.transfer pairedPartialFractionMap
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) =>
      ⟨hz,integerShiftScalar_upper z hz 1⟩) ⟨upperRadius,upperRadius_inside⟩
  intro z hz
  exact upperPairedPartialFractionValue_period_one z hz

theorem pairedPartialFractionDerivative_period_one (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedPartialFractionDerivative (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1)).val.Equiv
      (pairedPartialFractionDerivative z hz).val := by
  have hi := translatedPairedHolomorphic.derivative_unique pairedPartialFractionMap_holomorphic z hz
  have hd : (translatedPairedHolomorphic.derivative z hz).val.Equiv
      (pairedPartialFractionDerivative (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1)).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (translatedPairedHolomorphic.derivative z hz).property)
      (hright := (pairedPartialFractionDerivative (integerShiftScalar z 1)
        (integerShiftScalar_upper z hz 1)).property)
    let X := ComplexRawQuotient.ofRaw
      (pairedPartialFractionDerivative (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1)).val
      (pairedPartialFractionDerivative (integerShiftScalar z 1) (integerShiftScalar_upper z hz 1)).property
    change X*ComplexRawQuotient.ofQComplex ⟨((1:Int):Rat),0⟩=X
    rw [integer_constant]
    grind only
  exact equiv_trans (pairedPartialFractionDerivative (integerShiftScalar z 1)
    (integerShiftScalar_upper z hz 1)).property (translatedPairedHolomorphic.derivative z hz).property
    (pairedPartialFractionDerivative z hz).property (equiv_symm hd) hi

end ComputableAnalysis.ModularForms
