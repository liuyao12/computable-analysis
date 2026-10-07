import ComputableAnalysis.ModularForms.PairedUpperRiccatiHolomorphic

/-! Exact analytic derivative of the actual canonical Riccati expression. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedUpperRiccatiDerivative (z : Scalar) (hu : InUpperHalfPlane z.val) : Scalar :=
  let p := pairedPartialFractionMap.eval z hu
  let d := pairedPartialFractionDerivative z hu
  let pd := DomainFunctions.scalarProduct p d
  scalarSum (pairedCanonicalSecondDerivative z hu) (scalarSum pd pd)

theorem pairedUpperRiccatiMap_derivative (z : Scalar) (hu : InUpperHalfPlane z.val) :
    (pairedUpperRiccatiMap_holomorphic.derivative z hu).val.Equiv
      (pairedUpperRiccatiDerivative z hu).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedUpperRiccatiMap_holomorphic.derivative z hu).property)
    (hright := (pairedUpperRiccatiDerivative z hu).property)
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hu).val
    (pairedPartialFractionMap.eval z hu).property
  let D := ComplexRawQuotient.ofRaw (pairedPartialFractionDerivative z hu).val
    (pairedPartialFractionDerivative z hu).property
  let DD := ComplexRawQuotient.ofRaw (pairedCanonicalSecondDerivative z hu).val
    (pairedCanonicalSecondDerivative z hu).property
  change DD+(D*P+P*D)=DD+(P*D+P*D)
  grind only

noncomputable def pairedUpperRiccatiMap_hasDerivativeAt (z : Scalar) (hu : InUpperHalfPlane z.val) :
    HasDerivativeAt pairedUpperRiccatiMap z hu (pairedUpperRiccatiDerivative z hu) :=
  (pairedUpperRiccatiMap_holomorphic.atPoint z hu).congrDerivative (pairedUpperRiccatiMap_derivative z hu)

end ComputableAnalysis.ModularForms
