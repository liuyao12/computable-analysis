import ComputableAnalysis.ModularForms.PairedReciprocalSquareTail
import ComputableAnalysis.ModularForms.LatticeDerivativeNomeQuotient

/-! Actual reciprocal-square sum, independent of cutoff, and its nome quotient. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedReciprocalSquareAssembly (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) : Scalar :=
  let i := upperIntegerReciprocal z hz 0
  scalarSum (scalarProduct i i)
    ⟨add (ScalarSeries.block (fun n => (upperPairedReciprocalSquare z hz (n+1)).val) 0 (4*B))
      (pairedReciprocalSquareTailValue z hz B),
      add_valid (ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalSquare z hz (n+1)).property) 0 (4*B))
        (pairedReciprocalSquareTailValue_valid z hz B hB)⟩

theorem pairedReciprocalSquareAssembly_joined_derivative (z : Scalar)
    (hz : InUpperHalfPlane z.val) (B : Nat) (hB : Small z.val (B:Rat)) :
    (pairedReciprocalSquareAssembly z hz B hB).val.Equiv
      (neg (pairedWholeJoinedDerivative B z ⟨hz,hB⟩).val) := by
  let i := upperIntegerReciprocal z hz 0
  let c := (integerReciprocalMap_holomorphic 0).derivative z hz
  let f := (pairedFiniteMap_holomorphic (4*B)).derivative z hz
  let p := ScalarSeries.block (fun n => (upperPairedReciprocalDerivative z hz (n+1)).val) 0 (4*B)
  let s := ScalarSeries.block (fun n => (upperPairedReciprocalSquare z hz (n+1)).val) 0 (4*B)
  let t := pairedDerivativeTailValue z hz B
  let u := pairedReciprocalSquareTailValue z hz B
  have vp := ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalDerivative z hz (n+1)).property) 0 (4*B)
  have vs := ScalarSeries.block_valid _ (fun n => (upperPairedReciprocalSquare z hz (n+1)).property) 0 (4*B)
  have vt := pairedDerivativeTailValue_valid z hz B hB
  have vu := pairedReciprocalSquareTailValue_valid z hz B hB
  have hc := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := c.property)
    (hright := (ReciprocalDifference.derivative (integerShiftScalar z 0)
      (upperScalar_nonzero _ (integerShiftScalar_upper z hz 0))).property)
    (integerReciprocalMap_derivative 0 z hz)
  have hf := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := f.property) (hright := vp)
    (pairedFiniteMap_derivative (4*B) z hz)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vs) (hright := neg_valid vp)
    (upperPairedReciprocalSquare_prefix_derivative z hz (4*B))
  have hu := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := vu) (hright := neg_valid vt)
    (pairedReciprocalSquareTailValue_derivative z hz B hB)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedReciprocalSquareAssembly z hz B hB).property)
    (hright := neg_valid (pairedWholeJoinedDerivative B z ⟨hz,hB⟩).property)
  let I := gridScalarValue i
  let C := gridScalarValue c
  let F := gridScalarValue f
  let P := ComplexRawQuotient.ofRaw p vp
  let S := ComplexRawQuotient.ofRaw s vs
  let T := ComplexRawQuotient.ofRaw t vt
  let U := ComplexRawQuotient.ofRaw u vu
  change C= -(I*I) at hc
  change F=P at hf
  change S= -P at hs
  change U= -T at hu
  change I*I+(S+U)= -(C+(F+T))
  generalize I=a, C=b, F=c, P=d, S=e, T=f, U=g at hc hf hs hu ⊢
  grind only

def pairedReciprocalSquareSum (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  pairedReciprocalSquareAssembly z hz (pairedDerivativeCutoff z) (pairedDerivativeCutoff_small z)

theorem pairedReciprocalSquareSum_derivative (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedReciprocalSquareSum z hz).val.Equiv (neg (pairedPartialFractionDerivative z hz).val) :=
  pairedReciprocalSquareAssembly_joined_derivative z hz _ (pairedDerivativeCutoff_small z)

theorem pairedReciprocalSquareAssembly_agreement (z : Scalar)
    (hz : InUpperHalfPlane z.val) (B : Nat) (hroom : Small z.val ((B:Rat)-1)) :
    (pairedReciprocalSquareAssembly z hz B (pairedCutoff_room_small B z hroom)).val.Equiv
      (pairedReciprocalSquareSum z hz).val := by
  have he := equiv_trans
    (pairedReciprocalSquareAssembly z hz B (pairedCutoff_room_small B z hroom)).property
    (neg_valid (pairedWholeJoinedDerivative B z ⟨hz,pairedCutoff_room_small B z hroom⟩).property)
    (neg_valid (pairedPartialFractionDerivative z hz).property)
    (pairedReciprocalSquareAssembly_joined_derivative z hz B (pairedCutoff_room_small B z hroom))
    (neg_equiv (pairedPartialFractionDerivative_cutoff B z hz hroom))
  exact equiv_trans
    (pairedReciprocalSquareAssembly z hz B (pairedCutoff_room_small B z hroom)).property
    (neg_valid (pairedPartialFractionDerivative z hz).property)
    (pairedReciprocalSquareSum z hz).property he
    (equiv_symm (pairedReciprocalSquareSum_derivative z hz))

theorem pairedReciprocalSquareSum_nome_quotient (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (pairedReciprocalSquareSum z hz).val.Equiv
      (neg (scaleRat 4 (mul (mul latticeFrequency.val latticeFrequency.val)
        (mul (nome.eval z hz).val
          (mul (RepresentedReciprocal.inverse (nomeDenominator (nome.eval z hz))
            (nome_upper_denominator_nonzero z hz)).val
            (RepresentedReciprocal.inverse (nomeDenominator (nome.eval z hz))
              (nome_upper_denominator_nonzero z hz)).val))))) := by
  let d := pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z (pairedGlobalOffPole_upper_mem z hz)
  let q := nome.eval z hz
  let j := RepresentedReciprocal.inverse (nomeDenominator q) (nome_upper_denominator_nonzero z hz)
  let r := scaleRat 4 (mul (mul latticeFrequency.val latticeFrequency.val)
    (mul q.val (mul j.val j.val)))
  have vr : r.Valid := scaleRat_valid (mul_valid (mul_valid latticeFrequency.property latticeFrequency.property)
    (mul_valid q.property (mul_valid j.property j.property)))
  have hd := pairedGlobalOffPoleAssemblyMap_upper_derivative_agreement z hz
  exact equiv_trans (pairedReciprocalSquareSum z hz).property
    (neg_valid (pairedPartialFractionDerivative z hz).property) (neg_valid vr)
    (pairedReciprocalSquareSum_derivative z hz)
    (equiv_trans (neg_valid (pairedPartialFractionDerivative z hz).property) (neg_valid d.property)
      (neg_valid vr) (neg_equiv (equiv_symm hd)) (neg_equiv (latticeDerivative_nome_quotient z hz)))

theorem pairedReciprocalSquareSum_congr (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) :
    (pairedReciprocalSquareSum z hz).val.Equiv (pairedReciprocalSquareSum w hw).val :=
  equiv_trans (pairedReciprocalSquareSum z hz).property
    (neg_valid (pairedPartialFractionDerivative z hz).property) (pairedReciprocalSquareSum w hw).property
    (pairedReciprocalSquareSum_derivative z hz)
    (equiv_trans (neg_valid (pairedPartialFractionDerivative z hz).property)
      (neg_valid (pairedPartialFractionDerivative w hw).property) (pairedReciprocalSquareSum w hw).property
      (neg_equiv (pairedPartialFractionDerivative_congr z w hz hw he))
      (equiv_symm (pairedReciprocalSquareSum_derivative w hw)))

end ComputableAnalysis.ModularForms
