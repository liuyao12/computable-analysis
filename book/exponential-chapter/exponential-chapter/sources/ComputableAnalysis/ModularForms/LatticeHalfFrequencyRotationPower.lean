import ComputableAnalysis.ModularForms.LatticeHalfFrequencyRotationInput
import ComputableAnalysis.ModularForms.ExponentialPowers

/-! The actual half-frequency rotation is a fourth root of unity. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem latticeFrequency_imaginary_product :
    (mul latticeImaginaryUnit.val latticeFrequency.val).Equiv
      (imaginaryAxis latticeFrequency.val.realPart) := by
  let r := ofRealRaw latticeFrequency.val.realPart
  have hr : r.Valid := ofRealRaw_valid _ (realPart_valid latticeFrequency.property)
  have hm := mul_equiv latticeImaginaryUnit.property latticeImaginaryUnit.property
    latticeFrequency.property hr (equiv_refl _ latticeImaginaryUnit.property) latticeFrequency_real_embedding
  have hq := qcomplexLeftMul_equiv_mul_ofQComplex ⟨0,1⟩ hr
  have he : (qcomplexLeftMul ⟨0,1⟩ r).Equiv (imaginaryAxis latticeFrequency.val.realPart) := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).2
    have hc : ((qcomplexLeftMul ⟨0,1⟩ r).compute n)=
        ((imaginaryAxis latticeFrequency.val.realPart).compute n) := by
      change (add (scaleRat 0 r) (scaleRat 1 (mulI r))).compute n=_
      dsimp [r,imaginaryAxis,ofRealRaw,mulI,scaleRat,add,QBox.scaleRat,QBox.add,QComplex.add]
      simp only [if_pos (show (0:Rat)≤1 by decide +kernel),Rat.neg_zero,Rat.zero_mul,Rat.one_mul,Rat.zero_add,Rat.add_zero]
    rw [hc]
    have ho := valid_ordered (imaginaryAxis_valid (realPart_valid latticeFrequency.property)) n
    exact ⟨ho,ho⟩
  have hqi := equiv_trans (imaginaryAxis_valid (realPart_valid latticeFrequency.property))
    (qcomplexLeftMul_valid ⟨0,1⟩ hr) (mul_valid latticeImaginaryUnit.property hr) (equiv_symm he) hq
  exact equiv_trans (mul_valid latticeImaginaryUnit.property latticeFrequency.property)
    (mul_valid latticeImaginaryUnit.property hr) (imaginaryAxis_valid (realPart_valid latticeFrequency.property))
    hm (equiv_symm hqi)

def latticeHalfFrequencyImaginary : Scalar :=
  ⟨imaginaryAxis latticeHalfFrequencyRotationInput.raw,imaginaryAxis_valid latticeHalfFrequencyRotationInput.valid⟩

theorem latticeHalfFrequency_fourfold_exponent :
    (scaleRat 4 latticeHalfFrequencyImaginary.val).Equiv latticeRotationSlope.val := by
  have hh := imaginaryAxis_equiv latticeHalfFrequencyRotationInput.valid
    (RealRaw.scaleRat_valid (realPart_valid latticeFrequency.property)) latticeHalfFrequencyRotationInput_agreement
  have hs := scaleRat_equiv (r := 4) hh
  have he : (scaleRat 4 (imaginaryAxis (RealRaw.scaleRat (1/2) latticeFrequency.val.realPart))).Equiv
      (add (imaginaryAxis latticeFrequency.val.realPart) (imaginaryAxis latticeFrequency.val.realPart)) := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).2
    have hc : (scaleRat 4 (imaginaryAxis (RealRaw.scaleRat (1/2) latticeFrequency.val.realPart))).compute n=
        (add (imaginaryAxis latticeFrequency.val.realPart) (imaginaryAxis latticeFrequency.val.realPart)).compute n := by
      dsimp [scaleRat,imaginaryAxis,mulI,ofRealRaw,RealRaw.scaleRat,RealRaw.scaleRatCompute,QBox.scaleRat,add,QBox.add,QComplex.add]
      simp only [Rat.neg_zero,Rat.mul_zero,Rat.zero_add]
      congr 1 <;> congr 1 <;> grind only
    rw [hc]
    have ho := valid_ordered (add_valid (imaginaryAxis_valid (realPart_valid latticeFrequency.property))
      (imaginaryAxis_valid (realPart_valid latticeFrequency.property))) n
    exact ⟨ho,ho⟩
  have hs' := equiv_trans (scaleRat_valid latticeHalfFrequencyImaginary.property)
    (scaleRat_valid (imaginaryAxis_valid (RealRaw.scaleRat_valid (realPart_valid latticeFrequency.property))))
    (add_valid (imaginaryAxis_valid (realPart_valid latticeFrequency.property))
      (imaginaryAxis_valid (realPart_valid latticeFrequency.property))) hs he
  have hp := add_equiv (equiv_symm latticeFrequency_imaginary_product)
    (equiv_symm latticeFrequency_imaginary_product)
  exact equiv_trans (scaleRat_valid latticeHalfFrequencyImaginary.property)
    (add_valid (imaginaryAxis_valid (realPart_valid latticeFrequency.property))
      (imaginaryAxis_valid (realPart_valid latticeFrequency.property))) latticeRotationSlope.property hs' hp

theorem latticeHalfFrequency_rotation_fourth_one :
    (LocalODE.power (RotationLift.HalfPiInput.rotation latticeHalfFrequencyRotationInput) 4).Equiv
      (ofQComplex QComplex.one) := by
  have hp := entireExponential_nat_multiple latticeHalfFrequencyImaginary 4
  have hx := entireExponentialValue_congr
    ⟨scaleRat 4 latticeHalfFrequencyImaginary.val,scaleRat_valid latticeHalfFrequencyImaginary.property⟩
    latticeRotationSlope latticeHalfFrequency_fourfold_exponent
  have hc : ((4:Nat):Rat)=(4:Rat) := by decide +kernel
  rw [hc] at hp
  have hr := LocalODE.power_congr _ _ (entireExponentialValue latticeHalfFrequencyImaginary).property
    (RotationLift.HalfPiInput.rotation_valid latticeHalfFrequencyRotationInput)
    latticeHalfFrequency_exponential_rotation 4
  exact equiv_trans (LocalODE.power_valid _ (RotationLift.HalfPiInput.rotation_valid latticeHalfFrequencyRotationInput) 4)
    (LocalODE.power_valid _ (entireExponentialValue latticeHalfFrequencyImaginary).property 4)
    (ofQComplex_valid _) (equiv_symm hr)
    (equiv_trans (LocalODE.power_valid _ (entireExponentialValue latticeHalfFrequencyImaginary).property 4)
      (entireExponentialValue ⟨scaleRat 4 latticeHalfFrequencyImaginary.val,
        scaleRat_valid latticeHalfFrequencyImaginary.property⟩).property (ofQComplex_valid _)
      (equiv_symm hp)
      (equiv_trans (entireExponentialValue ⟨scaleRat 4 latticeHalfFrequencyImaginary.val,
        scaleRat_valid latticeHalfFrequencyImaginary.property⟩).property
        (entireExponentialValue latticeRotationSlope).property (ofQComplex_valid _) hx latticeFrequency_exponential_period))

end ComputableAnalysis.ModularForms
