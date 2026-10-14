import ComputableAnalysis.ModularForms.IntegerPowerRowQuintic

/-! Actual sextic row from differentiation of the quintic identity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def quinticRowNumeratorMap : DomainFunctions.Map :=
  sumOn (productOn (integerPowerRowMap 2 (by omega)) (integerPowerRowMap 3 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
    (productOn pairedPartialFractionMap (integerPowerRowMap 4 (by omega))
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
def quinticRowNumeratorMap_holomorphic : Holomorphic quinticRowNumeratorMap :=
  ((integerPowerRowMap_holomorphic 2 (by omega)).productOn (integerPowerRowMap_holomorphic 3 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)).sumOn
    (pairedPartialFractionMap_holomorphic.productOn (integerPowerRowMap_holomorphic 4 (by omega))
      (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
def doubleQuinticRowMap : DomainFunctions.Map :=
  sumOn (integerPowerRowMap 5 (by omega)) (integerPowerRowMap 5 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)
def doubleQuinticRowMap_holomorphic : Holomorphic doubleQuinticRowMap :=
  (integerPowerRowMap_holomorphic 5 (by omega)).sumOn (integerPowerRowMap_holomorphic 5 (by omega))
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

private theorem sc2 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 2 x

private theorem sc3 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 3 x=(3:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 3 x

private theorem sc4 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 4 x=(4:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 4 x

private theorem sc5 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 5 x=(5:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 5 x

private theorem sc10 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 10 x=(10:ScalarAlgebra.Value)*x := ScalarAlgebra.scale_natural 10 x

theorem doubleQuinticRowMap_numerator (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (doubleQuinticRowMap.eval z hz).val.Equiv (quinticRowNumeratorMap.eval z hz).val := by
  have hf := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 5 (by omega)).property)
    (hright := (quinticRowFormula z hz).property) (integerReciprocalPowerRowSum_quintic z hz)
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let R2 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let R3 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 3 (by omega)).val
    (integerReciprocalPowerRowSum z hz 3 (by omega)).property
  let R4 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 4 (by omega)).val
    (integerReciprocalPowerRowSum z hz 4 (by omega)).property
  let R5 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 5 (by omega)).val
    (integerReciprocalPowerRowSum z hz 5 (by omega)).property
  let R6 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 6 (by omega)).val
    (integerReciprocalPowerRowSum z hz 6 (by omega)).property
  change R5=ComplexRawQuotient.scaleRat (1/2) (R2*R3+P*R4) at hf
  have ht := congrArg (ComplexRawQuotient.scaleRat 2) hf
  rw [ComplexRawQuotient.scaleRat_scaleRat,show (2:Rat)*(1/2)=1 by decide +kernel,
    ComplexRawQuotient.scaleRat_one,sc2] at ht
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (doubleQuinticRowMap.eval z hz).property)
    (hright := (quinticRowNumeratorMap.eval z hz).property)
  change R5+R5=R2*R3+P*R4
  generalize P=p,R2=r2,R3=r3,R4=r4,R5=r5 at ht ⊢
  grind only

def sexticRowFormula (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  let r2 := integerReciprocalPowerRowSum z hz 2 (by omega)
  let r3 := integerReciprocalPowerRowSum z hz 3 (by omega)
  let r4 := integerReciprocalPowerRowSum z hz 4 (by omega)
  let r5 := integerReciprocalPowerRowSum z hz 5 (by omega)
  let p := pairedPartialFractionMap.eval z hz
  ⟨scaleRat (1/5) (add (add (mul r3.val r3.val) (scaleRat 2 (mul r2.val r4.val)))
    (scaleRat 2 (mul p.val r5.val))),
    scaleRat_valid (r := (1/5:Rat)) (add_valid
      (add_valid (mul_valid r3.property r3.property)
        (scaleRat_valid (r := 2) (mul_valid r2.property r4.property)))
      (scaleRat_valid (r := 2) (mul_valid p.property r5.property)))⟩

theorem integerReciprocalPowerRowSum_sextic (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (integerReciprocalPowerRowSum z hz 6 (by omega)).val.Equiv (sexticRowFormula z hz).val := by
  have hd := doubleQuinticRowMap_holomorphic.derivative_equiv_on_overlap quinticRowNumeratorMap_holomorphic
    (fun z hz _ => doubleQuinticRowMap_numerator z hz) z hz hz
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (doubleQuinticRowMap_holomorphic.derivative z hz).property)
    (hright := (quinticRowNumeratorMap_holomorphic.derivative z hz).property) hd
  have h2 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 2 (by omega) z hz).property)
    (integerPowerRowMap_holomorphic_derivative 2 (by omega) z hz)
  have h3 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 3 (by omega) z hz).property)
    (integerPowerRowMap_holomorphic_derivative 3 (by omega) z hz)
  have h4 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 4 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 4 (by omega) z hz).property)
    (integerPowerRowMap_holomorphic_derivative 4 (by omega) z hz)
  have h5 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((integerPowerRowMap_holomorphic 5 (by omega)).derivative z hz).property)
    (hright := (integerPowerRowSlope 5 (by omega) z hz).property)
    (integerPowerRowMap_holomorphic_derivative 5 (by omega) z hz)
  have hp := equiv_trans (integerReciprocalPowerRowSum z hz 2 (by omega)).property
    (pairedReciprocalSquareSum z hz).property (neg_valid (pairedPartialFractionDerivative z hz).property)
    (integerReciprocalPowerRowSum_square_agreement z hz) (pairedReciprocalSquareSum_derivative z hz)
  have hP := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 2 (by omega)).property)
    (hright := neg_valid (pairedPartialFractionDerivative z hz).property) hp
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let R2 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let R3 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 3 (by omega)).val
    (integerReciprocalPowerRowSum z hz 3 (by omega)).property
  let R4 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 4 (by omega)).val
    (integerReciprocalPowerRowSum z hz 4 (by omega)).property
  let R5 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 5 (by omega)).val
    (integerReciprocalPowerRowSum z hz 5 (by omega)).property
  let R6 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 6 (by omega)).val
    (integerReciprocalPowerRowSum z hz 6 (by omega)).property
  let D2 := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 2 (by omega)).derivative z hz).property
  let D3 := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 3 (by omega)).derivative z hz).property
  let D4 := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 4 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 4 (by omega)).derivative z hz).property
  let D5 := ComplexRawQuotient.ofRaw ((integerPowerRowMap_holomorphic 5 (by omega)).derivative z hz).val
    ((integerPowerRowMap_holomorphic 5 (by omega)).derivative z hz).property
  let D := ComplexRawQuotient.ofRaw (pairedPartialFractionMap_holomorphic.derivative z hz).val
    (pairedPartialFractionMap_holomorphic.derivative z hz).property
  change D5+D5=(D2*R3+R2*D3)+(D*R4+P*D4) at he
  change R2= -D at hP
  change D2= -ComplexRawQuotient.scaleRat 2 R3 at h2
  rw [sc2] at h2
  change D3= -ComplexRawQuotient.scaleRat 3 R4 at h3
  rw [sc3] at h3
  change D4= -ComplexRawQuotient.scaleRat 4 R5 at h4
  rw [sc4] at h4
  change D5= -ComplexRawQuotient.scaleRat 5 R6 at h5
  rw [sc5] at h5
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerReciprocalPowerRowSum z hz 6 (by omega)).property)
    (hright := (sexticRowFormula z hz).property)
  change R6=ComplexRawQuotient.scaleRat (1/5)
    ((R3*R3+ComplexRawQuotient.scaleRat 2 (R2*R4))+ComplexRawQuotient.scaleRat 2 (P*R5))
  rw [sc2,sc2]
  generalize P=p,D=d,R2=r2,R3=r3,R4=r4,R5=r5,R6=r6,D2=d2,D3=d3,D4=d4,D5=d5 at he h2 h3 h4 h5 hP ⊢
  have hnum : (10:ScalarAlgebra.Value)*r6=(2:ScalarAlgebra.Value)*
      ((r3*r3+(2:ScalarAlgebra.Value)*(r2*r4))+(2:ScalarAlgebra.Value)*(p*r5)) := by grind only
  rw [← sc10,← sc2] at hnum
  have hdiv := congrArg (ComplexRawQuotient.scaleRat (1/10)) hnum
  simpa only [ComplexRawQuotient.scaleRat_scaleRat,show (1/10:Rat)*10=1 by decide +kernel,
    show (1/10:Rat)*2=1/5 by decide +kernel,ComplexRawQuotient.scaleRat_one] using hdiv

def sexticRowRiccatiFormula (z : Scalar) (hz : InUpperHalfPlane z.val) : Scalar :=
  let r2 := integerReciprocalPowerRowSum z hz 2 (by omega)
  let p := pairedPartialFractionMap.eval z hz
  let c := pairedRiccatiCenterConstant
  let pp := scalarProduct p p
  let poly := scalarSum
    ⟨sub (scaleRat 15 (LocalODE.power p.val 4)) (scaleRat 15 (mul c.val pp.val)),
      sub_valid (scaleRat_valid (r := 15) (LocalODE.power_valid _ p.property 4))
        (scaleRat_valid (r := 15) (mul_valid c.property pp.property))⟩
    ⟨scaleRat 2 (mul c.val c.val),scaleRat_valid (r := 2) (mul_valid c.property c.property)⟩
  ⟨scaleRat (1/15) (mul r2.val poly.val),scaleRat_valid (r := (1/15:Rat)) (mul_valid r2.property poly.property)⟩

private theorem sc15 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 15 x=(15:ScalarAlgebra.Value)*x :=
  ScalarAlgebra.scale_natural 15 x

private theorem sextic_algebra (p c u v w : ScalarAlgebra.Value)
    (ha : ((3:ScalarAlgebra.Value)*p*p-2*c)*(3*u)=
      ((3:ScalarAlgebra.Value)*p*p-2*c)*((p*p+ -c)*(p*p+ -c)+2*(p*(p*(p*p+ -c)))))
    (hb : (3:ScalarAlgebra.Value)*p*(2*v)=3*p*((p*p+ -c)*(p*(p*p+ -c))+p*u))
    (hc : (3:ScalarAlgebra.Value)*(5*w)=3*((p*(p*p+ -c))*(p*(p*p+ -c))+2*((p*p+ -c)*u)+2*(p*v))) :
    (15:ScalarAlgebra.Value)*w=(p*p+ -c)*((15*p^4-15*(c*(p*p)))+2*(c*c)) := by
  have hn (x : ScalarAlgebra.Value) : (15:ScalarAlgebra.Value)*x=3*(5*x) := by
    clear ha hb hc
    grind only
  calc
    15*w = 3*((p*(p*p+ -c))*(p*(p*p+ -c))+2*((p*p+ -c)*u)+2*(p*v)) := (hn w).trans hc
    _ = 3*(p*(p*p+ -c))*(p*(p*p+ -c))+6*(p*p+ -c)*u+3*p*(2*v) := by
      clear ha hb hc; grind only
    _ = 3*(p*(p*p+ -c))*(p*(p*p+ -c))+6*(p*p+ -c)*u+3*p*((p*p+ -c)*(p*(p*p+ -c))+p*u) := by rw [hb]
    _ = (3*p*p-2*c)*(3*u)+6*p*p*(p*p+ -c)*(p*p+ -c) := by
      clear ha hb hc; grind only
    _ = (3*p*p-2*c)*((p*p+ -c)*(p*p+ -c)+2*(p*(p*(p*p+ -c))))+6*p*p*(p*p+ -c)*(p*p+ -c) := by rw [ha]
    _ = (p*p+ -c)*((15*p^4-15*(c*(p*p)))+2*(c*c)) := by
      clear ha hb hc; grind only

theorem integerReciprocalPowerRowSum_sextic_riccati (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (integerReciprocalPowerRowSum z hz 6 (by omega)).val.Equiv (sexticRowRiccatiFormula z hz).val := by
  have h4 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 4 (by omega)).property)
    (hright := (quarticRowFormula z hz).property) (integerReciprocalPowerRowSum_quartic z hz)
  have h5 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 5 (by omega)).property)
    (hright := (quinticRowFormula z hz).property) (integerReciprocalPowerRowSum_quintic z hz)
  have h6 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 6 (by omega)).property)
    (hright := (sexticRowFormula z hz).property) (integerReciprocalPowerRowSum_sextic z hz)
  have h2 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 2 (by omega)).property)
    (hright := (squareRowRiccatiFormulaMap.eval z hz).property) (integerPowerRow_square_riccati_formula z hz)
  have h3 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (integerReciprocalPowerRowSum z hz 3 (by omega)).property)
    (hright := mul_valid (pairedPartialFractionMap.eval z hz).property
      (integerReciprocalPowerRowSum z hz 2 (by omega)).property) (integerReciprocalPowerRowSum_cubic z hz)
  let P := ComplexRawQuotient.ofRaw (pairedPartialFractionMap.eval z hz).val (pairedPartialFractionMap.eval z hz).property
  let C := ComplexRawQuotient.ofRaw pairedRiccatiCenterConstant.val pairedRiccatiCenterConstant.property
  let R2 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 2 (by omega)).val
    (integerReciprocalPowerRowSum z hz 2 (by omega)).property
  let R3 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 3 (by omega)).val
    (integerReciprocalPowerRowSum z hz 3 (by omega)).property
  let R4 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 4 (by omega)).val
    (integerReciprocalPowerRowSum z hz 4 (by omega)).property
  let R5 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 5 (by omega)).val
    (integerReciprocalPowerRowSum z hz 5 (by omega)).property
  let R6 := ComplexRawQuotient.ofRaw (integerReciprocalPowerRowSum z hz 6 (by omega)).val
    (integerReciprocalPowerRowSum z hz 6 (by omega)).property
  change R2=P*P+ -C at h2
  change R3=P*R2 at h3
  change R4=ComplexRawQuotient.scaleRat (1/3) (R2*R2+ComplexRawQuotient.scaleRat 2 (P*R3)) at h4
  change R5=ComplexRawQuotient.scaleRat (1/2) (R2*R3+P*R4) at h5
  change R6=ComplexRawQuotient.scaleRat (1/5)
    ((R3*R3+ComplexRawQuotient.scaleRat 2 (R2*R4))+ComplexRawQuotient.scaleRat 2 (P*R5)) at h6
  have hh4 := congrArg (ComplexRawQuotient.scaleRat 3) h4
  have hh5 := congrArg (ComplexRawQuotient.scaleRat 2) h5
  have hh6 := congrArg (ComplexRawQuotient.scaleRat 5) h6
  rw [ComplexRawQuotient.scaleRat_scaleRat,show (3:Rat)*(1/3)=1 by decide +kernel,
    ComplexRawQuotient.scaleRat_one,sc2,sc3] at hh4
  rw [ComplexRawQuotient.scaleRat_scaleRat,show (2:Rat)*(1/2)=1 by decide +kernel,
    ComplexRawQuotient.scaleRat_one,sc2] at hh5
  rw [ComplexRawQuotient.scaleRat_scaleRat,show (5:Rat)*(1/5)=1 by decide +kernel,
    ComplexRawQuotient.scaleRat_one,sc2,sc2,sc5] at hh6
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerReciprocalPowerRowSum z hz 6 (by omega)).property)
    (hright := (sexticRowRiccatiFormula z hz).property)
  change R6=ComplexRawQuotient.scaleRat (1/15) (R2*
    ((ComplexRawQuotient.scaleRat 15
      (ComplexRawQuotient.ofRaw (LocalODE.power (pairedPartialFractionMap.eval z hz).val 4)
        (LocalODE.power_valid _ (pairedPartialFractionMap.eval z hz).property 4))-
      ComplexRawQuotient.scaleRat 15 (C*(P*P)))+ComplexRawQuotient.scaleRat 2 (C*C)))
  rw [ScalarAlgebra.ofRaw_power]
  change R6=ComplexRawQuotient.scaleRat (1/15) (R2*
    ((ComplexRawQuotient.scaleRat 15 (P^4)-ComplexRawQuotient.scaleRat 15 (C*(P*P)))+
      ComplexRawQuotient.scaleRat 2 (C*C)))
  rw [sc15,sc15,sc2]
  generalize P=p,C=c,R2=r2,R3=r3,R4=r4,R5=r5,R6=r6 at h2 h3 hh4 hh5 hh6 ⊢
  have hnum : (15:ScalarAlgebra.Value)*r6=r2*
      (((15:ScalarAlgebra.Value)*p^4-(15:ScalarAlgebra.Value)*(c*(p*p)))+(2:ScalarAlgebra.Value)*(c*c)) := by
    rw [h3,h2] at hh4 hh5 hh6
    rw [h2]
    have ha := congrArg (fun x : ScalarAlgebra.Value => ((3:ScalarAlgebra.Value)*p*p-(2:ScalarAlgebra.Value)*c)*x) hh4
    have hb := congrArg (fun x : ScalarAlgebra.Value => (3:ScalarAlgebra.Value)*p*x) hh5
    have hc := congrArg (fun x : ScalarAlgebra.Value => (3:ScalarAlgebra.Value)*x) hh6
    exact sextic_algebra p c r4 r5 r6 ha hb hc
  rw [← sc15] at hnum
  have hdiv := congrArg (ComplexRawQuotient.scaleRat (1/15)) hnum
  simpa only [ComplexRawQuotient.scaleRat_scaleRat,show (1/15:Rat)*15=1 by decide +kernel,
    ComplexRawQuotient.scaleRat_one] using hdiv

end ComputableAnalysis.ModularForms
