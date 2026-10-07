import ComputableAnalysis.ModularForms.PairedLaurentReciprocalEquation

/-! Actual second derivative of the pole-regularized lattice reciprocal. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def regularizedReciprocalOpenData : ScalarTopology.OpenData pairedRegularizedLaurentReciprocalMap.domain :=
  ⟨pairedRegularizedLaurentReciprocalMap.domain_congr,
    pairedRegularizedLaurentReciprocalMap_holomorphic.openDomain.radius,
    pairedRegularizedLaurentReciprocalMap_holomorphic.openDomain.inside⟩

def regularizedReciprocalRhsMap : DomainFunctions.Map :=
  sumOn (constantOn _ regularizedReciprocalOpenData.invariant ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩)
    (negate (productOn (constantOn _ regularizedReciprocalOpenData.invariant pairedRiccatiCenterConstant)
      (productOn pairedRegularizedLaurentReciprocalMap pairedRegularizedLaurentReciprocalMap (fun _ hz => hz))
      (fun _ hz => hz))) (fun _ hz => hz)

def regularizedReciprocalRhsMap_holomorphic : Holomorphic regularizedReciprocalRhsMap :=
  (constantOn_holomorphic regularizedReciprocalOpenData ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩).sumOn
    ((constantOn_holomorphic regularizedReciprocalOpenData pairedRiccatiCenterConstant).productOn
      (pairedRegularizedLaurentReciprocalMap_holomorphic.productOn
        pairedRegularizedLaurentReciprocalMap_holomorphic (fun _ hz => hz)) (fun _ hz => hz)).negate
    (fun _ hz => hz)

def pairedRegularizedLaurentReciprocal_derivative_holomorphic :
    Holomorphic (derivativeMap pairedRegularizedLaurentReciprocalMap
      pairedRegularizedLaurentReciprocalMap_holomorphic) :=
  regularizedReciprocalRhsMap_holomorphic.transfer _ (fun _ hz => hz)
    ⟨pairedRegularizedLaurentReciprocalMap_holomorphic.openDomain.radius,
      pairedRegularizedLaurentReciprocalMap_holomorphic.openDomain.inside⟩
    (fun z hz => equiv_symm (pairedRegularizedLaurentReciprocal_differential_identity z hz))

theorem pairedRegularizedLaurentReciprocal_second_derivative (z : Scalar)
    (hz : LocalODE.interior (1/32) z) :
    (pairedRegularizedLaurentReciprocal_derivative_holomorphic.derivative z hz).val.Equiv
      (neg (add
        (mul (mul pairedRiccatiCenterConstant.val (pairedRegularizedLaurentReciprocalMap.eval z hz).val)
          (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).val)
        (mul (mul pairedRiccatiCenterConstant.val (pairedRegularizedLaurentReciprocalMap.eval z hz).val)
          (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedRegularizedLaurentReciprocal_derivative_holomorphic.derivative z hz).property)
    (hright := neg_valid (add_valid
      (mul_valid (mul_valid pairedRiccatiCenterConstant.property (pairedRegularizedLaurentReciprocalMap.eval z hz).property)
        (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).property)
      (mul_valid (mul_valid pairedRiccatiCenterConstant.property (pairedRegularizedLaurentReciprocalMap.eval z hz).property)
        (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).property)))
  let C := gridScalarValue pairedRiccatiCenterConstant
  let W := gridScalarValue (pairedRegularizedLaurentReciprocalMap.eval z hz)
  let D := gridScalarValue (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz)
  change 0+ -(0*(W*W)+C*(D*W+W*D))= -((C*W)*D+(C*W)*D)
  grind only

theorem pairedRegularizedLaurentReciprocal_second_derivative_center (z : Scalar)
    (hz : LocalODE.interior (1/32) z) (he : z.val.Equiv zero) :
    (pairedRegularizedLaurentReciprocal_derivative_holomorphic.derivative z hz).val.Equiv zero := by
  have hs := pairedRegularizedLaurentReciprocal_second_derivative z hz
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularizedLaurentReciprocalMap.eval z hz).property) (hright := ofQComplex_valid _)
    (pairedRegularizedLaurentReciprocal_center z hz he)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedRegularizedLaurentReciprocal_derivative_holomorphic.derivative z hz).property)
    (hright := ofQComplex_valid _)
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedRegularizedLaurentReciprocal_derivative_holomorphic.derivative z hz).property)
    (hright := neg_valid (add_valid
      (mul_valid (mul_valid pairedRiccatiCenterConstant.property (pairedRegularizedLaurentReciprocalMap.eval z hz).property)
        (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).property)
      (mul_valid (mul_valid pairedRiccatiCenterConstant.property (pairedRegularizedLaurentReciprocalMap.eval z hz).property)
        (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz).property))) hs
  let W := gridScalarValue (pairedRegularizedLaurentReciprocalMap.eval z hz)
  let C := gridScalarValue pairedRiccatiCenterConstant
  let D := gridScalarValue (pairedRegularizedLaurentReciprocalMap_holomorphic.derivative z hz)
  change _= -((C*W)*D+(C*W)*D) at hh
  change W=0 at hv
  change _=(0:ScalarAlgebra.Value)
  rw [hh,hv]
  grind only

end ComputableAnalysis.ModularForms
