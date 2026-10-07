import ComputableAnalysis.ModularForms.IntegerPowerRowCubic

/-! Actual quartic reciprocal row from the differentiated cubic product identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def cubicRowProductMap : DomainFunctions.Map :=
  productOn pairedPartialFractionMap (integerPowerRowMap 2 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def cubicRowProductMap_holomorphic : Holomorphic cubicRowProductMap :=
  pairedPartialFractionMap_holomorphic.productOn (integerPowerRowMap_holomorphic 2 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def quarticRowFormula (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  let r2 := integerReciprocalPowerRowSum z hz 2 (by omega)
  let r3 := integerReciprocalPowerRowSum z hz 3 (by omega)
  let p := pairedPartialFractionMap.eval z hz
  ⟨scaleRat (1/3) (add (mul r2.val r2.val) (scaleRat 2 (mul p.val r3.val))),
    scaleRat_valid (r := (1/3:Rat)) (add_valid (mul_valid r2.property r2.property)
      (scaleRat_valid (r := 2) (mul_valid p.property r3.property)))⟩

theorem integerReciprocalPowerRowSum_quartic (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (integerReciprocalPowerRowSum z hz 4 (by omega)).val.Equiv (quarticRowFormula z hz).val := by
  have hd := (integerPowerRowMap_holomorphic 3 (by omega)).derivative_equiv_on_overlap
    cubicRowProductMap_holomorphic (fun z hz _ => integerReciprocalPowerRowSum_cubic z hz) z hz hz
  have hn := integerPowerRowMap_holomorphic_derivative 3 (by omega) z hz
  have h2 := integerPowerRowMap_holomorphic_derivative 2 (by omega) z hz
  have hp := equiv_trans (integerReciprocalPowerRowSum z hz 2 (by omega)).property
    (pairedReciprocalSquareSum z hz).property (neg_valid (pairedPartialFractionDerivative z hz).property)
    (integerReciprocalPowerRowSum_square_agreement z hz) (pairedReciprocalSquareSum_derivative z hz)
  have heD := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).property)
    (hright := (cubicRowProductMap_holomorphic.derivative z hz).property) hd
  have heN := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 3 (by omega) z hz).property) hn
  have he2 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 2 (by omega) z hz).property) h2
  have heP := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 2 (by omega)).property)
    (hright := neg_valid (pairedPartialFractionDerivative z hz).property) hp
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerReciprocalPowerRowSum z hz 4 (by omega)).property)
    (hright := (quarticRowFormula z hz).property)
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let D := ComplexRawQuotient.ofRaw (pairedPartialFractionMap_holomorphic.derivative z hz).val
    (pairedPartialFractionMap_holomorphic.derivative z hz).property
  let R2 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let R3 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 3 (by omega)).val
    (integerReciprocalPowerRowSum z hz 3 (by omega)).property
  let R4 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 4 (by omega)).val
    (integerReciprocalPowerRowSum z hz 4 (by omega)).property
  let D2 := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property
  let E := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).property
  change E=D*R2+P*D2 at heD
  change E= -ComplexRawQuotient.scaleRat 3 R4 at heN
  change D2= -ComplexRawQuotient.scaleRat 2 R3 at he2
  change R2= -D at heP
  have hscale2 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x :=
    ScalarAlgebra.scale_natural 2 x
  have hscale3 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x :=
    ScalarAlgebra.scale_natural 3 x
  rw [hscale3] at heN
  rw [hscale2] at he2
  change R4=ComplexRawQuotient.scaleRat (1/3) (R2*R2+ComplexRawQuotient.scaleRat 2 (P*R3))
  rw [hscale2]
  generalize P=p,D=d,R2=r2,R3=r3,R4=r4,D2=d2,E=e at heD heN he2 heP ⊢
  have hthree : (3:ScalarAlgebra.Value)*r4=r2*r2+(2:ScalarAlgebra.Value)*(p*r3) := by grind only
  rw [← hscale3] at hthree
  have hthird := congrArg (ComplexRawQuotient.scaleRat (1/3)) hthree
  simpa only [ComplexRawQuotient.scaleRat_scaleRat,
    show (1/3:Rat)*3=1 by decide +kernel,ComplexRawQuotient.scaleRat_one] using hthird

def quarticRowRiccatiFormula (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  let r2 := integerReciprocalPowerRowSum z hz 2 (by omega)
  let p := pairedPartialFractionMap.eval z hz
  ⟨scaleRat (1/3) (mul r2.val (sub (scaleRat 3 (mul p.val p.val)) pairedRiccatiCenterConstant.val)),
    scaleRat_valid (r := (1/3:Rat)) (mul_valid r2.property
      (sub_valid (scaleRat_valid (r := 3) (mul_valid p.property p.property)) pairedRiccatiCenterConstant.property))⟩

theorem integerReciprocalPowerRowSum_quartic_riccati (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (integerReciprocalPowerRowSum z hz 4 (by omega)).val.Equiv (quarticRowRiccatiFormula z hz).val := by
  apply equiv_trans (integerReciprocalPowerRowSum z hz 4 (by omega)).property
    (quarticRowFormula z hz).property (quarticRowRiccatiFormula z hz).property
    (integerReciprocalPowerRowSum_quartic z hz)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 2 (by omega)).property)
    (hright := (squareRowRiccatiFormulaMap.eval z hz).property) (integerPowerRow_square_riccati_formula z hz)
  have hc := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 3 (by omega)).property)
    (hright := mul_valid (pairedPartialFractionMap.eval z hz).property
      (integerReciprocalPowerRowSum z hz 2 (by omega)).property) (integerReciprocalPowerRowSum_cubic z hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (quarticRowFormula z hz).property) (hright := (quarticRowRiccatiFormula z hz).property)
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let C := ComplexRawQuotient.ofRaw pairedRiccatiCenterConstant.val pairedRiccatiCenterConstant.property
  let R2 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let R3 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 3 (by omega)).val
    (integerReciprocalPowerRowSum z hz 3 (by omega)).property
  change R2=P*P+ -C at hs
  change R3=P*R2 at hc
  change ComplexRawQuotient.scaleRat (1/3) (R2*R2+ComplexRawQuotient.scaleRat 2 (P*R3))=
    ComplexRawQuotient.scaleRat (1/3) (R2*(ComplexRawQuotient.scaleRat 3 (P*P)-C))
  congr 1
  have hscale2 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x :=
    ScalarAlgebra.scale_natural 2 x
  have hscale3 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x :=
    ScalarAlgebra.scale_natural 3 x
  rw [hscale2,hscale3]
  generalize P=p,C=c,R2=r2,R3=r3 at hs hc ⊢
  grind only

end ComputableAnalysis.ModularForms
