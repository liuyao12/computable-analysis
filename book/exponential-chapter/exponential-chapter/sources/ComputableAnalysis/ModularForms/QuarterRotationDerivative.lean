import ComputableAnalysis.RiemannHilbert.DomainAffineFunction
import ComputableAnalysis.ModularForms.ImaginaryUnit
import ComputableAnalysis.ModularForms.ExponentialDerivative
import ComputableAnalysis.ModularForms.RotationQuarterPositivity
import ComputableAnalysis.ModularForms.UpperHalfPlane

/-! The actual exponential's directional derivative has negative real
coordinate on the quarter-turn angle chart. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private def quarterScalarValue (z : Scalar) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw z.val z.property

def angleRotationMap : DomainFunctions.Map :=
  DomainFunctions.compose entireExponential
    (DomainFunctions.affine ⟨zero,ofQComplex_valid _⟩ latticeImaginaryUnit)

def angleRotationMap_holomorphic : DomainFunctions.Holomorphic angleRotationMap :=
  entireExponential_holomorphic.compose
    (DomainFunctions.affine_holomorphic ⟨zero,ofQComplex_valid _⟩ latticeImaginaryUnit)

theorem angleRotationMap_differential_identity (z : Scalar)
    (hz : angleRotationMap.domain z) :
    (angleRotationMap_holomorphic.derivative z hz).val.Equiv
      (mul latticeImaginaryUnit.val (angleRotationMap.eval z hz).val) := by
  let a := (DomainFunctions.affine ⟨zero,ofQComplex_valid _⟩ latticeImaginaryUnit).eval z trivial
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponential_holomorphic.derivative a trivial).property)
    (hright := (entireExponentialValue a).property) (entireExponential_derivative_value a)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (angleRotationMap_holomorphic.derivative z hz).property)
    (hright := mul_valid latticeImaginaryUnit.property (angleRotationMap.eval z hz).property)
  let D := quarterScalarValue (entireExponential_holomorphic.derivative a trivial)
  let E := quarterScalarValue (entireExponentialValue a)
  let I := quarterScalarValue latticeImaginaryUnit
  change D=E at hd
  change D*I=I*E
  rw [hd]
  grind only

theorem imaginary_unit_mul_negative_real (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    (RealRaw.neg (mul latticeImaginaryUnit.val z.val).realPart).Pos := by
  have he := qcomplexLeftMul_equiv_mul_ofQComplex ⟨0,1⟩ z.property
  have hp : (RealRaw.neg (qcomplexLeftMul ⟨0,1⟩ z.val).realPart).Pos := by
    obtain ⟨N,hN⟩ := hz
    refine ⟨N,?_⟩
    change 0 < (z.val.compute N).lo.im at hN
    change 0 < -((qcomplexLeftMul ⟨0,1⟩ z.val).compute N).hi.re
    change 0 < -((add (scaleRat 0 z.val) (scaleRat 1 (mulI z.val))).compute N).hi.re
    dsimp [add,scaleRat,mulI,QBox.add,QBox.scaleRat,QComplex.add]
    simp only [if_pos (show (0:Rat)≤1 by decide +kernel),Rat.zero_mul,Rat.one_mul,
      Rat.zero_add,Rat.neg_neg]
    exact hN
  exact positive_of_equiv
    (RealRaw.neg_valid (realPart_valid (qcomplexLeftMul_valid ⟨0,1⟩ z.property)))
    (RealRaw.neg_valid (realPart_valid (mul_valid latticeImaginaryUnit.property z.property)))
    (RealRaw.neg_equiv (realPart_equiv he)) hp

theorem quarter_rotation_directional_derivative_negative (A : RotationLift.HalfPiInput) :
    (RealRaw.neg (mul latticeImaginaryUnit.val
      (entireExponential_holomorphic.derivative
        ⟨imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩ trivial).val).realPart).Pos := by
  let z : Scalar := ⟨imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩
  let d := entireExponential_holomorphic.derivative z trivial
  have he := entireExponential_derivative_value z
  have hr := entireExponential_represented_rotation A
  have hd := equiv_trans d.property (entireExponentialValue z).property
    (RotationLift.HalfPiInput.rotation_valid A) he hr
  have hu : InUpperHalfPlane d.val :=
    (upperHalfPlane_congr d.property (RotationLift.HalfPiInput.rotation_valid A) hd).mpr
      (rotationQuarter_represented_positive A)
  exact imaginary_unit_mul_negative_real d hu

theorem angleRotationMap_real_input_agreement (A : RotationLift.HalfPiInput) :
    (angleRotationMap.eval ⟨ofRealRaw A.raw,ofRealRaw_valid _ A.valid⟩
      ⟨trivial,trivial⟩).val.Equiv (RotationLift.HalfPiInput.rotation A) := by
  let x : Scalar := ⟨ofRealRaw A.raw,ofRealRaw_valid _ A.valid⟩
  let a := (DomainFunctions.affine ⟨zero,ofQComplex_valid _⟩ latticeImaginaryUnit).eval x trivial
  let b : Scalar := ⟨imaginaryAxis A.raw,imaginaryAxis_valid A.valid⟩
  have hc : (qcomplexLeftMul ⟨0,1⟩ x.val).Equiv b.val := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).2
    have he : (qcomplexLeftMul ⟨0,1⟩ x.val).compute n=b.val.compute n := by
      change (add (scaleRat 0 x.val) (scaleRat 1 (mulI x.val))).compute n=_
      dsimp [x,b,imaginaryAxis,ofRealRaw,mulI,scaleRat,add,QBox.scaleRat,QBox.add,QComplex.add]
      simp only [if_pos (show (0:Rat)≤1 by decide +kernel),Rat.zero_mul,Rat.one_mul,
        Rat.zero_add,Rat.add_zero]
    rw [he]
    have ho := valid_ordered b.property n
    exact ⟨ho,ho⟩
  have hq := qcomplexLeftMul_equiv_mul_ofQComplex ⟨0,1⟩ x.property
  have hm := equiv_trans (mul_valid latticeImaginaryUnit.property x.property)
    (qcomplexLeftMul_valid ⟨0,1⟩ x.property) b.property (equiv_symm hq) hc
  have ha : a.val.Equiv (mul latticeImaginaryUnit.val x.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := a.property)
      (hright := mul_valid latticeImaginaryUnit.property x.property)
    change 0+quarterScalarValue latticeImaginaryUnit*quarterScalarValue x=
      quarterScalarValue latticeImaginaryUnit*quarterScalarValue x
    grind only
  have hab := equiv_trans a.property (mul_valid latticeImaginaryUnit.property x.property)
    b.property ha hm
  exact equiv_trans (entireExponentialValue a).property (entireExponentialValue b).property
    (RotationLift.HalfPiInput.rotation_valid A)
    (entireExponentialValue_congr a b hab) (entireExponential_represented_rotation A)

theorem angleRotationMap_real_derivative_negative (A : RotationLift.HalfPiInput) :
    (angleRotationMap_holomorphic.derivative
      ⟨ofRealRaw A.raw,ofRealRaw_valid _ A.valid⟩ ⟨trivial,trivial⟩).val.realPart.Neg := by
  let x : Scalar := ⟨ofRealRaw A.raw,ofRealRaw_valid _ A.valid⟩
  let e := angleRotationMap.eval x ⟨trivial,trivial⟩
  let d := angleRotationMap_holomorphic.derivative x ⟨trivial,trivial⟩
  have he := angleRotationMap_real_input_agreement A
  have hu : InUpperHalfPlane e.val :=
    (upperHalfPlane_congr e.property (RotationLift.HalfPiInput.rotation_valid A) he).mpr
      (rotationQuarter_represented_positive A)
  have hp := imaginary_unit_mul_negative_real e hu
  have hd := angleRotationMap_differential_identity x ⟨trivial,trivial⟩
  have hn := positive_of_equiv
    (RealRaw.neg_valid (realPart_valid (mul_valid latticeImaginaryUnit.property e.property)))
    (RealRaw.neg_valid (realPart_valid d.property))
    (RealRaw.neg_equiv (realPart_equiv (equiv_symm hd))) hp
  obtain ⟨N,hN⟩ := hn
  refine ⟨N,?_⟩
  change 0 < -(d.val.compute N).hi.re at hN
  change (d.val.compute N).hi.re < 0
  grind only

end ComputableAnalysis.ModularForms
