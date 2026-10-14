import ComputableAnalysis.ModularForms.IntegerPowerRowHolomorphic
import ComputableAnalysis.ModularForms.IntegerPowerSquareRows
import ComputableAnalysis.ModularForms.PairedNomeRiccatiDifference

/-! Cubic reciprocal row from actual row calculus and the proved Riccati identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def squareRowRiccatiFormulaMap : DomainFunctions.Map :=
  sumOn (productOn pairedPartialFractionMap pairedPartialFractionMap (fun _ hz => hz))
    (constantOn (fun z => InUpperHalfPlane z.val) upperOpenData.invariant (scalarNeg pairedRiccatiCenterConstant)) (fun _ hz => hz)

def squareRowRiccatiFormulaMap_holomorphic : Holomorphic squareRowRiccatiFormulaMap :=
  (pairedPartialFractionMap_holomorphic.productOn pairedPartialFractionMap_holomorphic
    (fun _ hz => hz)).sumOn (constantOn_holomorphic upperOpenData (scalarNeg pairedRiccatiCenterConstant))
    (fun _ hz => hz)

theorem integerPowerRow_square_riccati_formula (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (integerReciprocalPowerRowSum z hz 2 (by omega)).val.Equiv
      (squareRowRiccatiFormulaMap.eval z hz).val := by
  have hr := integerReciprocalPowerRowSum_square_agreement z hz
  have hs := pairedReciprocalSquareSum_derivative z hz
  have hd := pairedPartialFractionMap_riccati z hz
  have h := equiv_trans (integerReciprocalPowerRowSum z hz 2 (by omega)).property
    (pairedReciprocalSquareSum z hz).property
    (neg_valid (pairedPartialFractionDerivative z hz).property) hr hs
  have hq := equiv_trans (integerReciprocalPowerRowSum z hz 2 (by omega)).property
    (neg_valid (pairedPartialFractionDerivative z hz).property)
    (neg_valid (sub_valid pairedRiccatiCenterConstant.property
      (mul_valid (pairedPartialFractionMap.eval z hz).property (pairedPartialFractionMap.eval z hz).property)))
    h (neg_equiv hd)
  apply equiv_trans (integerReciprocalPowerRowSum z hz 2 (by omega)).property
    (neg_valid (sub_valid pairedRiccatiCenterConstant.property
      (mul_valid (pairedPartialFractionMap.eval z hz).property (pairedPartialFractionMap.eval z hz).property)))
    (squareRowRiccatiFormulaMap.eval z hz).property hq
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := neg_valid (sub_valid pairedRiccatiCenterConstant.property
      (mul_valid (pairedPartialFractionMap.eval z hz).property (pairedPartialFractionMap.eval z hz).property)))
    (hright := (squareRowRiccatiFormulaMap.eval z hz).property)
  let C := ComplexRawQuotient.ofRaw pairedRiccatiCenterConstant.val pairedRiccatiCenterConstant.property
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  change -(C-P*P)=P*P+ -C
  generalize C=c,P=p
  grind only

theorem integerReciprocalPowerRowSum_cubic (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (integerReciprocalPowerRowSum z hz 3 (by omega)).val.Equiv
      (mul (pairedPartialFractionMap.eval z hz).val (integerReciprocalPowerRowSum z hz 2 (by omega)).val) := by
  have hd := (integerPowerRowMap_holomorphic 2 (by omega)).derivative_equiv_on_overlap
    squareRowRiccatiFormulaMap_holomorphic (fun z hz _ => integerPowerRow_square_riccati_formula z hz) z hz hz
  have hnext := integerPowerRowMap_holomorphic_derivative 2 (by omega) z hz
  have hsquare := integerPowerRow_square_riccati_formula z hz
  have hric := pairedPartialFractionMap_riccati z hz
  have heD := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property)
    (hright := (squareRowRiccatiFormulaMap_holomorphic.derivative z hz).property) hd
  have heN := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 2 (by omega) z hz).property) hnext
  have heS := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 2 (by omega)).property)
    (hright := (squareRowRiccatiFormulaMap.eval z hz).property) hsquare
  have heR := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (pairedPartialFractionMap_holomorphic.derivative z hz).property)
    (hright := sub_valid pairedRiccatiCenterConstant.property
      (mul_valid (pairedPartialFractionMap.eval z hz).property (pairedPartialFractionMap.eval z hz).property)) hric
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerReciprocalPowerRowSum z hz 3 (by omega)).property)
    (hright := mul_valid (pairedPartialFractionMap.eval z hz).property (integerReciprocalPowerRowSum z hz 2 (by omega)).property)
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let D := ComplexRawQuotient.ofRaw (pairedPartialFractionMap_holomorphic.derivative z hz).val
    (pairedPartialFractionMap_holomorphic.derivative z hz).property
  let C := ComplexRawQuotient.ofRaw pairedRiccatiCenterConstant.val pairedRiccatiCenterConstant.property
  let R2 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let R3 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 3 (by omega)).val
    (integerReciprocalPowerRowSum z hz 3 (by omega)).property
  let E := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property
  change E=(D*P+P*D)+0 at heD
  change E= -ComplexRawQuotient.scaleRat 2 R3 at heN
  change R2=P*P+ -C at heS
  change D=C-P*P at heR
  have hc : ComplexRawQuotient.scaleRat 2 R3=(2:ScalarAlgebra.Value)*R3 := ScalarAlgebra.scale_natural 2 R3
  rw [hc] at heN
  change R3=P*R2
  generalize P=p,D=d,C=c,R2=r2,R3=r3,E=e at heD heN heS heR ⊢
  have htwo : (2:ScalarAlgebra.Value)*r3=(2:ScalarAlgebra.Value)*(p*r2) := by grind only
  have hscale (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x :=
    ScalarAlgebra.scale_natural 2 x
  rw [← hscale r3,← hscale (p*r2)] at htwo
  have hhalf := congrArg (ComplexRawQuotient.scaleRat (1/2)) htwo
  simpa only [ComplexRawQuotient.scaleRat_scaleRat,
    show (1/2:Rat)*2=1 by decide +kernel,ComplexRawQuotient.scaleRat_one] using hhalf

end ComputableAnalysis.ModularForms
