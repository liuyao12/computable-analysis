import ComputableAnalysis.ModularForms.NomeUpperCotangent

/-! Normalization of the actual nome kernel for lattice comparison. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def nomeCotangentScale : Scalar :=
  ⟨scaleRat (-1/2) nomeSlope.val,scaleRat_valid nomeSlope.property⟩

def normalizedNomeCotangentMap : DomainFunctions.Map :=
  compose (affine ⟨zero,ofQComplex_valid _⟩ nomeCotangentScale) upperNomeCotangentMap

def normalizedNomeCotangentMap_holomorphic : Holomorphic normalizedNomeCotangentMap :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ nomeCotangentScale).compose
    upperNomeCotangentMap_holomorphic

def normalizedNomeCotangentDerivative (z : Scalar) (hz : normalizedNomeCotangentMap.domain z) : Scalar :=
  DomainFunctions.scalarProduct nomeCotangentScale (upperNomeCotangentDerivative z (compose_inner_mem hz))

theorem normalizedNomeCotangentMap_derivative (z : Scalar) (hz : normalizedNomeCotangentMap.domain z) :
    (normalizedNomeCotangentMap_holomorphic.derivative z hz).val.Equiv
      (normalizedNomeCotangentDerivative z hz).val :=
  mul_equiv nomeCotangentScale.property nomeCotangentScale.property
    (upperNomeCotangentMap_holomorphic.derivative z (compose_inner_mem hz)).property
    (upperNomeCotangentDerivative z (compose_inner_mem hz)).property
    (equiv_refl _ nomeCotangentScale.property) (upperNomeCotangentMap_derivative z (compose_inner_mem hz))

theorem normalizedNomeCotangent_riccati (z : Scalar) (hz : normalizedNomeCotangentMap.domain z) :
    (normalizedNomeCotangentDerivative z hz).val.Equiv
      (sub (scaleRat (1/4) (mul nomeSlope.val nomeSlope.val))
        (mul (normalizedNomeCotangentMap.eval z hz).val (normalizedNomeCotangentMap.eval z hz).val)) := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid (upperNomeCotangentDerivative z (compose_inner_mem hz)).property
      (upperNomeCotangentDerivative z (compose_inner_mem hz)).property)
    (hright := mul_valid nomeSlope.property (sub_valid
      (mul_valid (upperNomeCotangentMap.eval z (compose_inner_mem hz)).property
        (upperNomeCotangentMap.eval z (compose_inner_mem hz)).property) (ofQComplex_valid _)))
    (upperNomeCotangent_differential_identity z (compose_inner_mem hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (normalizedNomeCotangentDerivative z hz).property)
    (hright := sub_valid (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
      (mul_valid (normalizedNomeCotangentMap.eval z hz).property (normalizedNomeCotangentMap.eval z hz).property))
  let A := ComplexRawQuotient.ofRaw nomeSlope.val nomeSlope.property
  let F := ComplexRawQuotient.ofRaw (upperNomeCotangentMap.eval z (compose_inner_mem hz)).val
    (upperNomeCotangentMap.eval z (compose_inner_mem hz)).property
  let D := ComplexRawQuotient.ofRaw (upperNomeCotangentDerivative z (compose_inner_mem hz)).val
    (upperNomeCotangentDerivative z (compose_inner_mem hz)).property
  change D+D=A*(F*F-1) at he
  change ComplexRawQuotient.scaleRat (-1/2) A*D = ComplexRawQuotient.scaleRat (1/4) (A*A) -
    (0+ComplexRawQuotient.scaleRat (-1/2) A*F)*(0+ComplexRawQuotient.scaleRat (-1/2) A*F)
  have h := congrArg (ComplexRawQuotient.scaleRat (-1/4)) he
  rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.add_scaleRat] at h
  have hc : (-1/4:Rat)+(-1/4)= -1/2 := by decide +kernel
  rw [hc] at h
  rw [← ComplexRawQuotient.scaleRat_mul]
  rw [← ComplexRawQuotient.mul_scaleRat, h]
  have hzero : (0:ComplexRawQuotient.Value)+ComplexRawQuotient.scaleRat (-1/2) A*F = ComplexRawQuotient.scaleRat (-1/2) A*F := by grind only
  rw [hzero]
  rw [← ComplexRawQuotient.scaleRat_mul,ComplexRawQuotient.scaleRat_mul_scaleRat]
  have hc2 : (-1/2:Rat)*(-1/2)=1/4 := by decide +kernel
  rw [hc2]
  have halg : A*(F*F-1) = A*(F*F)-A := by grind only
  have halg2 : (A*F)*(A*F) = A*(A*(F*F)) := by grind only
  rw [halg,halg2]
  have hs1 : A*(F*F)-A = A*(F*F)+(-A) := by grind only
  have hs2 : ComplexRawQuotient.scaleRat (1/4) (A*A) - ComplexRawQuotient.scaleRat (1/4) (A*(A*(F*F))) = ComplexRawQuotient.scaleRat (1/4) (A*A) + (-ComplexRawQuotient.scaleRat (1/4) (A*(A*(F*F)))) := by grind only
  rw [hs1,hs2]
  simp only [ComplexRawQuotient.scaleRat_add,
    ComplexRawQuotient.neg_eq_scaleRat_neg_one,ComplexRawQuotient.scaleRat_scaleRat]
  have hdistr : A*(ComplexRawQuotient.scaleRat (-1/4) (A*(F*F)) + ComplexRawQuotient.scaleRat (-1/4 * -1) A) =
      A*ComplexRawQuotient.scaleRat (-1/4) (A*(F*F)) + A*ComplexRawQuotient.scaleRat (-1/4 * -1) A := by grind only
  rw [hdistr,ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.mul_scaleRat]
  have hc3 : (-1/4:Rat)*(-1)=1/4 := by decide +kernel
  have hc4 : (-1:Rat)*(1/4)= -1/4 := by decide +kernel
  rw [hc3,hc4]
  grind only

end ComputableAnalysis.ModularForms
