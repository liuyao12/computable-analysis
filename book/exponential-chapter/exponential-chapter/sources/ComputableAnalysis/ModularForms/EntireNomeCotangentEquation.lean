import ComputableAnalysis.ModularForms.NomeHalfPeriodValue
import ComputableAnalysis.ModularForms.NomeRiccatiConstant

/-! The actual nome cotangent extension and its differential equation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem entireNomeCotangent_upper_mem (z : Scalar) (hu : InUpperHalfPlane z.val) :
    entireNomeCotangentMap.domain z := by
  let q := entireNomeMap.eval z (entireNomeMap_mem z)
  have he := entireNomeMap_upper_agreement z hu
  exact ⟨entireNomeMap_mem z,(cotangentRationalMap.domain_congr q (nome.eval z hu) he).mpr
    ((cotangentRationalMap_domain _).mpr (nome_upper_denominator_nonzero z hu))⟩

theorem entireNomeCotangent_upper_agreement (z : Scalar) (hu : InUpperHalfPlane z.val) :
    (entireNomeCotangentMap.eval z (entireNomeCotangent_upper_mem z hu)).val.Equiv
      (upperNomeCotangentMap.eval z hu).val :=
  cotangentRationalMap.eval_congr _ _ _ _ (entireNomeMap_upper_agreement z hu)

theorem entireNomeCotangent_differential_identity (z : Scalar)
    (hz : entireNomeCotangentMap.domain z) :
    (add (entireNomeCotangentMap_holomorphic.derivative z hz).val
      (entireNomeCotangentMap_holomorphic.derivative z hz).val).Equiv
      (mul nomeSlope.val
        (sub (mul (entireNomeCotangentMap.eval z hz).val (entireNomeCotangentMap.eval z hz).val)
          (ofQComplex QComplex.one))) := by
  let q := entireNomeMap.eval z (compose_inner_mem hz)
  let hq := compose_outer_mem hz
  let j := nomeRationalInverseMap.eval q hq
  let a := (affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval z trivial
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (nomeDenominator q).property j.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse (nomeDenominator q) (compose_outer_mem hq))
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponential_holomorphic.derivative a trivial).property) (hright := q.property)
    (entireExponential_derivative_value a)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (entireNomeCotangentMap_holomorphic.derivative z hz).property
      (entireNomeCotangentMap_holomorphic.derivative z hz).property)
    (hright := mul_valid nomeSlope.property (sub_valid
      (mul_valid (entireNomeCotangentMap.eval z hz).property (entireNomeCotangentMap.eval z hz).property)
      (ofQComplex_valid _)))
  let Q := gridScalarValue q
  let J := gridScalarValue j
  let A := gridScalarValue nomeSlope
  let E := gridScalarValue (entireExponential_holomorphic.derivative a trivial)
  change (1-Q)*J=1 at hj
  change E=Q at hd
  change (((( -(J*J))*(-1))*(1+1*Q)+J*1)*(E*A))+
    (((( -(J*J))*(-1))*(1+1*Q)+J*1)*(E*A)) =
    A*((J*(1+1*Q))*(J*(1+1*Q))-1)
  rw [hd]
  grind only

def entireNormalizedNomeCotangentMap : DomainFunctions.Map :=
  compose (affine ⟨zero,ofQComplex_valid _⟩ nomeCotangentScale) entireNomeCotangentMap

def entireNormalizedNomeCotangentMap_holomorphic : Holomorphic entireNormalizedNomeCotangentMap :=
  (affine_holomorphic ⟨zero,ofQComplex_valid _⟩ nomeCotangentScale).compose
    entireNomeCotangentMap_holomorphic

theorem entireNormalizedNomeCotangent_riccati (z : Scalar) (hz : entireNormalizedNomeCotangentMap.domain z) :
    (entireNormalizedNomeCotangentMap_holomorphic.derivative z hz).val.Equiv
      (sub (scaleRat (1/4) (mul nomeSlope.val nomeSlope.val))
        (mul (entireNormalizedNomeCotangentMap.eval z hz).val (entireNormalizedNomeCotangentMap.eval z hz).val)) := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid (entireNomeCotangentMap_holomorphic.derivative z (compose_inner_mem hz)).property
      (entireNomeCotangentMap_holomorphic.derivative z (compose_inner_mem hz)).property)
    (hright := mul_valid nomeSlope.property (sub_valid
      (mul_valid (entireNomeCotangentMap.eval z (compose_inner_mem hz)).property
        (entireNomeCotangentMap.eval z (compose_inner_mem hz)).property) (ofQComplex_valid _)))
    (entireNomeCotangent_differential_identity z (compose_inner_mem hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (entireNormalizedNomeCotangentMap_holomorphic.derivative z hz).property)
    (hright := sub_valid (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
      (mul_valid (entireNormalizedNomeCotangentMap.eval z hz).property (entireNormalizedNomeCotangentMap.eval z hz).property))
  let A := ComplexRawQuotient.ofRaw nomeSlope.val nomeSlope.property
  let F := ComplexRawQuotient.ofRaw (entireNomeCotangentMap.eval z (compose_inner_mem hz)).val
    (entireNomeCotangentMap.eval z (compose_inner_mem hz)).property
  let D := ComplexRawQuotient.ofRaw (entireNomeCotangentMap_holomorphic.derivative z (compose_inner_mem hz)).val
    (entireNomeCotangentMap_holomorphic.derivative z (compose_inner_mem hz)).property
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

theorem entireNormalizedNomeCotangent_halfPeriod_mem :
    entireNormalizedNomeCotangentMap.domain latticeHalfPoint :=
  ⟨entireNomeCotangent_halfPeriod_mem,trivial⟩

theorem entireNormalizedNomeCotangent_halfPeriod_zero :
    (entireNormalizedNomeCotangentMap.eval latticeHalfPoint
      entireNormalizedNomeCotangent_halfPeriod_mem).val.Equiv zero := by
  have hf := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireNomeCotangentMap.eval latticeHalfPoint entireNomeCotangent_halfPeriod_mem).property)
    (hright := ofQComplex_valid _) entireNomeCotangent_halfPeriod_zero
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (entireNormalizedNomeCotangentMap.eval latticeHalfPoint
      entireNormalizedNomeCotangent_halfPeriod_mem).property) (hright := ofQComplex_valid _)
  let F := gridScalarValue (entireNomeCotangentMap.eval latticeHalfPoint entireNomeCotangent_halfPeriod_mem)
  let B := gridScalarValue nomeCotangentScale
  change F=0 at hf
  change 0+B*F=(0:ScalarAlgebra.Value)
  rw [hf]
  grind only

theorem entireNormalizedNomeCotangent_halfPeriod_derivative :
    (entireNormalizedNomeCotangentMap_holomorphic.derivative latticeHalfPoint
      entireNormalizedNomeCotangent_halfPeriod_mem).val.Equiv
      (scaleRat (1/4) (mul nomeSlope.val nomeSlope.val)) := by
  let hz := entireNormalizedNomeCotangent_halfPeriod_mem
  let v := entireNormalizedNomeCotangentMap.eval latticeHalfPoint hz
  let d := entireNormalizedNomeCotangentMap_holomorphic.derivative latticeHalfPoint hz
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v.property) (hright := ofQComplex_valid _)
    entireNormalizedNomeCotangent_halfPeriod_zero
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property)
    (hright := sub_valid (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
      (mul_valid v.property v.property)) (entireNormalizedNomeCotangent_riccati latticeHalfPoint hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property)
    (hright := scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
  let V := gridScalarValue v
  let D := gridScalarValue d
  let K := ComplexRawQuotient.ofRaw (scaleRat (1/4) (mul nomeSlope.val nomeSlope.val))
    (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
  change V=0 at hv
  change D=K-V*V at hd
  change D=K
  rw [hv] at hd
  grind only

end ComputableAnalysis.ModularForms
