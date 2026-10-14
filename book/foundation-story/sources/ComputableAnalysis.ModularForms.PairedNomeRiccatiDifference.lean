import ComputableAnalysis.ModularForms.PairedEntireRiccatiConstancy
import ComputableAnalysis.ModularForms.NomeRiccatiConstant

/-! The actual lattice and nome kernels satisfy a proved difference equation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem normalizedNomeCotangent_upper_mem (z : Scalar) (hz : InUpperHalfPlane z.val) :
    normalizedNomeCotangentMap.domain z := ⟨hz,trivial⟩

theorem pairedUpperRiccatiValue_center_identity (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedUpperRiccatiValue z hz).val.Equiv pairedRiccatiCenterConstant.val :=
  equiv_trans (pairedUpperRiccatiValue z hz).property
    (pairedGlobalOffPoleRiccatiMap.eval z (pairedGlobalOffPole_upper_mem z hz)).property
    pairedRiccatiCenterConstant.property
    (equiv_symm (pairedGlobalOffPoleRiccatiMap_upper_agreement z hz))
    (pairedGlobalOffPoleRiccatiMap_center_identity z (pairedGlobalOffPole_upper_mem z hz))

theorem pairedPartialFractionMap_riccati (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedPartialFractionMap_holomorphic.derivative z hz).val.Equiv
      (sub pairedRiccatiCenterConstant.val
        (mul (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).val)) := by
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedUpperRiccatiValue z hz).property)
    (hright := pairedRiccatiCenterConstant.property) (pairedUpperRiccatiValue_center_identity z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedPartialFractionMap_holomorphic.derivative z hz).property)
    (hright := sub_valid pairedRiccatiCenterConstant.property
      (mul_valid (pairedPartialFractionMap.eval z hz).property (pairedPartialFractionMap.eval z hz).property))
  let D := gridScalarValue (pairedPartialFractionMap_holomorphic.derivative z hz)
  let P := gridScalarValue (pairedPartialFractionMap.eval z hz)
  let C := gridScalarValue pairedRiccatiCenterConstant
  change D+P*P=C at hh
  change D=C-P*P
  grind only

def pairedNomeDifferenceMap : DomainFunctions.Map :=
  sumOn pairedPartialFractionMap (negate normalizedNomeCotangentMap)
    (fun z hz => normalizedNomeCotangent_upper_mem z hz)

def pairedNomeDifferenceMap_holomorphic : Holomorphic pairedNomeDifferenceMap :=
  pairedPartialFractionMap_holomorphic.sumOn normalizedNomeCotangentMap_holomorphic.negate
    (fun z hz => normalizedNomeCotangent_upper_mem z hz)

def pairedNomeRiccatiConstantDifference : Scalar :=
  gridScalarSub pairedRiccatiCenterConstant
    ⟨scaleRat (1/4) (mul nomeSlope.val nomeSlope.val),
      scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property)⟩

theorem pairedNomeDifferenceMap_differential_identity (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedNomeDifferenceMap_holomorphic.derivative z hz).val.Equiv
      (sub pairedNomeRiccatiConstantDifference.val
        (mul (add (pairedPartialFractionMap.eval z hz).val
          (normalizedNomeCotangentMap.eval z (normalizedNomeCotangent_upper_mem z hz)).val)
          (pairedNomeDifferenceMap.eval z hz).val)) := by
  let hn := normalizedNomeCotangent_upper_mem z hz
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedPartialFractionMap_holomorphic.derivative z hz).property)
    (hright := sub_valid pairedRiccatiCenterConstant.property
      (mul_valid (pairedPartialFractionMap.eval z hz).property (pairedPartialFractionMap.eval z hz).property))
    (pairedPartialFractionMap_riccati z hz)
  have hd := equiv_trans (normalizedNomeCotangentMap_holomorphic.derivative z hn).property
    (normalizedNomeCotangentDerivative z hn).property
    (sub_valid (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
      (mul_valid (normalizedNomeCotangentMap.eval z hn).property (normalizedNomeCotangentMap.eval z hn).property))
    (normalizedNomeCotangentMap_derivative z hn) (normalizedNomeCotangent_riccati z hn)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (normalizedNomeCotangentMap_holomorphic.derivative z hn).property)
    (hright := sub_valid (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
      (mul_valid (normalizedNomeCotangentMap.eval z hn).property (normalizedNomeCotangentMap.eval z hn).property)) hd
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedNomeDifferenceMap_holomorphic.derivative z hz).property)
    (hright := sub_valid pairedNomeRiccatiConstantDifference.property
      (mul_valid (add_valid (pairedPartialFractionMap.eval z hz).property
        (normalizedNomeCotangentMap.eval z hn).property) (pairedNomeDifferenceMap.eval z hz).property))
  let P := gridScalarValue (pairedPartialFractionMap.eval z hz)
  let Q := gridScalarValue (normalizedNomeCotangentMap.eval z hn)
  let DP := gridScalarValue (pairedPartialFractionMap_holomorphic.derivative z hz)
  let DQ := gridScalarValue (normalizedNomeCotangentMap_holomorphic.derivative z hn)
  let C := gridScalarValue pairedRiccatiCenterConstant
  let K := ComplexRawQuotient.ofRaw (scaleRat (1/4) (mul nomeSlope.val nomeSlope.val))
    (scaleRat_valid (mul_valid nomeSlope.property nomeSlope.property))
  change DP=C-P*P at hp
  change DQ=K-Q*Q at hq
  change DP+ -DQ=(C-K)-(P+Q)*(P+ -Q)
  rw [hp,hq]
  grind only

end ComputableAnalysis.ModularForms
