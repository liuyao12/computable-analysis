import ComputableAnalysis.ModularForms.IntegerPowerRowQuartic

/-! Actual quintic row from differentiation of the quartic identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def row2SquareMap := productOn (integerPowerRowMap 2 (by omega))
  (integerPowerRowMap 2 (by omega)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
private def row2SquareMap_holomorphic : Holomorphic row2SquareMap :=
  (integerPowerRowMap_holomorphic 2 (by omega)).productOn (integerPowerRowMap_holomorphic 2 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
private def pRow3Map := productOn pairedPartialFractionMap (integerPowerRowMap 3 (by omega))
  (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
private def pRow3Map_holomorphic : Holomorphic pRow3Map :=
  pairedPartialFractionMap_holomorphic.productOn (integerPowerRowMap_holomorphic 3 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def quarticRowNumeratorMap : DomainFunctions.Map := sumOn row2SquareMap
  (sumOn pRow3Map pRow3Map (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
  (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
def quarticRowNumeratorMap_holomorphic : Holomorphic quarticRowNumeratorMap :=
  row2SquareMap_holomorphic.sumOn
    (pRow3Map_holomorphic.sumOn pRow3Map_holomorphic (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
def tripleQuarticRowMap : DomainFunctions.Map := sumOn (integerPowerRowMap 4 (by omega))
  (sumOn (integerPowerRowMap 4 (by omega)) (integerPowerRowMap 4 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
  (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
def tripleQuarticRowMap_holomorphic : Holomorphic tripleQuarticRowMap :=
  (integerPowerRowMap_holomorphic 4 (by omega)).sumOn
    ((integerPowerRowMap_holomorphic 4 (by omega)).sumOn (integerPowerRowMap_holomorphic 4 (by omega))
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

private theorem sc2 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x :=
  ScalarAlgebra.scale_natural 2 x
private theorem sc3 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x :=
  ScalarAlgebra.scale_natural 3 x
private theorem sc4 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 4 x=(4:ScalarAlgebra.Value)*x :=
  ScalarAlgebra.scale_natural 4 x
private theorem sc6 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 6 x=(6:ScalarAlgebra.Value)*x :=
  ScalarAlgebra.scale_natural 6 x
private theorem sc12 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 12 x=(12:ScalarAlgebra.Value)*x :=
  ScalarAlgebra.scale_natural 12 x

theorem tripleQuarticRowMap_numerator (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (tripleQuarticRowMap.eval z hz).val.Equiv (quarticRowNumeratorMap.eval z hz).val := by
  have hf := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 4 (by omega)).property)
    (hright := (quarticRowFormula z hz).property) (integerReciprocalPowerRowSum_quartic z hz)
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let R2 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let R3 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 3 (by omega)).val
    (integerReciprocalPowerRowSum z hz 3 (by omega)).property
  let R4 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 4 (by omega)).val
    (integerReciprocalPowerRowSum z hz 4 (by omega)).property
  change R4=ComplexRawQuotient.scaleRat (1/3) (R2*R2+ComplexRawQuotient.scaleRat 2 (P*R3)) at hf
  have ht := congrArg (ComplexRawQuotient.scaleRat 3) hf
  rw [ComplexRawQuotient.scaleRat_scaleRat,show (3:Rat)*(1/3)=1 by decide +kernel,
    ComplexRawQuotient.scaleRat_one,sc2,sc3] at ht
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (tripleQuarticRowMap.eval z hz).property)
    (hright := (quarticRowNumeratorMap.eval z hz).property)
  change R4+(R4+R4)=R2*R2+(P*R3+P*R3)
  generalize P=p,R2=r2,R3=r3,R4=r4 at ht ⊢
  grind only

def quinticRowFormula (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  let r2 := integerReciprocalPowerRowSum z hz 2 (by omega)
  let r3 := integerReciprocalPowerRowSum z hz 3 (by omega)
  let r4 := integerReciprocalPowerRowSum z hz 4 (by omega)
  let p := pairedPartialFractionMap.eval z hz
  ⟨scaleRat (1/2) (add (mul r2.val r3.val) (mul p.val r4.val)),
    scaleRat_valid (r := (1/2:Rat)) (add_valid (mul_valid r2.property r3.property) (mul_valid p.property r4.property))⟩

theorem integerReciprocalPowerRowSum_quintic (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (integerReciprocalPowerRowSum z hz 5 (by omega)).val.Equiv (quinticRowFormula z hz).val := by
  have hd := tripleQuarticRowMap_holomorphic.derivative_equiv_on_overlap quarticRowNumeratorMap_holomorphic
    (fun z hz _ => tripleQuarticRowMap_numerator z hz) z hz hz
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (tripleQuarticRowMap_holomorphic.derivative z hz).property)
    (hright := (quarticRowNumeratorMap_holomorphic.derivative z hz).property) hd
  have h2 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 2 (by omega) z hz).property) (integerPowerRowMap_holomorphic_derivative 2 (by omega) z hz)
  have h3 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 3 (by omega) z hz).property) (integerPowerRowMap_holomorphic_derivative 3 (by omega) z hz)
  have h4 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 4 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 4 (by omega) z hz).property) (integerPowerRowMap_holomorphic_derivative 4 (by omega) z hz)
  have hp := equiv_trans (integerReciprocalPowerRowSum z hz 2 (by omega)).property
    (pairedReciprocalSquareSum z hz).property (neg_valid (pairedPartialFractionDerivative z hz).property)
    (integerReciprocalPowerRowSum_square_agreement z hz) (pairedReciprocalSquareSum_derivative z hz)
  have hP := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 2 (by omega)).property)
    (hright := neg_valid (pairedPartialFractionDerivative z hz).property) hp
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let D := ComplexRawQuotient.ofRaw (pairedPartialFractionMap_holomorphic.derivative z hz).val
    (pairedPartialFractionMap_holomorphic.derivative z hz).property
  let R2 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let R3 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 3 (by omega)).val
    (integerReciprocalPowerRowSum z hz 3 (by omega)).property
  let R4 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 4 (by omega)).val
    (integerReciprocalPowerRowSum z hz 4 (by omega)).property
  let R5 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 5 (by omega)).val
    (integerReciprocalPowerRowSum z hz 5 (by omega)).property
  let D2 := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property
  let D3 := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).property
  let D4 := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 4 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 4 (by omega)).derivative z hz).property
  change D4+(D4+D4)=(D2*R2+R2*D2)+((D*R3+P*D3)+(D*R3+P*D3)) at he
  change D2= -ComplexRawQuotient.scaleRat 2 R3 at h2
  change D3= -ComplexRawQuotient.scaleRat 3 R4 at h3
  change D4= -ComplexRawQuotient.scaleRat 4 R5 at h4
  change R2= -D at hP
  rw [sc2] at h2
  rw [sc3] at h3
  rw [sc4] at h4
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerReciprocalPowerRowSum z hz 5 (by omega)).property)
    (hright := (quinticRowFormula z hz).property)
  change R5=ComplexRawQuotient.scaleRat (1/2) (R2*R3+P*R4)
  generalize P=p,D=d,R2=r2,R3=r3,R4=r4,R5=r5,D2=d2,D3=d3,D4=d4 at he h2 h3 h4 hP ⊢
  have hnum : (12:ScalarAlgebra.Value)*r5=(6:ScalarAlgebra.Value)*(r2*r3+p*r4) := by grind only
  rw [← sc12,← sc6] at hnum
  have hdiv := congrArg (ComplexRawQuotient.scaleRat (1/12)) hnum
  simpa only [ComplexRawQuotient.scaleRat_scaleRat,show (1/12:Rat)*12=1 by decide +kernel,
    show (1/12:Rat)*6=1/2 by decide +kernel,ComplexRawQuotient.scaleRat_one] using hdiv

end ComputableAnalysis.ModularForms
