import ComputableAnalysis.ModularForms.ImaginaryUnitAlgebra

/-! The quadratic equation of the executable CM point. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert
set_option maxRecDepth 8192

def cmPoint163Value : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw cmPoint163 cmPoint163_valid

private def halfValue : ScalarAlgebra.Value := ComplexRawQuotient.scaleRat (1/2) 1

private theorem half_twice : halfValue+halfValue=1 := by
  unfold halfValue
  rw [ComplexRawQuotient.add_scaleRat]
  have h : (1/2:Rat)+1/2=1 := by decide +kernel
  rw [h,ComplexRawQuotient.scaleRat_one]

theorem cmPoint163Value_formula :
    cmPoint163Value=ComplexRawQuotient.scaleRat (1/2)
      (1+imaginaryUnitValue*sqrt163Value) := by
  have hi := mulI_class (⟨sqrt163Complex,sqrt163Complex_valid⟩ : Scalar)
  change ComplexRawQuotient.ofRaw (ComplexRaw.imaginaryAxis sqrt163)
    (ComplexRaw.imaginaryAxis_valid sqrt163_valid)=imaginaryUnitValue*sqrt163Value at hi
  change ComplexRawQuotient.scaleRat (1/2)
    (1+ComplexRawQuotient.ofRaw (ComplexRaw.imaginaryAxis sqrt163)
      (ComplexRaw.imaginaryAxis_valid sqrt163_valid)) = _
  rw [hi]

theorem cmPoint163Value_quadratic :
    cmPoint163Value*cmPoint163Value=cmPoint163Value-41 := by
  have hform := cmPoint163Value_formula
  have hscale : ComplexRawQuotient.scaleRat (1/2)
      (1+imaginaryUnitValue*sqrt163Value)=halfValue*(1+imaginaryUnitValue*sqrt163Value) := by
    unfold halfValue
    rw [← ComplexRawQuotient.scaleRat_mul]
    congr 1
    grind
  rw [hscale] at hform
  have hs := sqrt163Value_square
  have hi := imaginaryUnitValue_square
  have hh := half_twice
  have ht : 2*(cmPoint163Value*cmPoint163Value-cmPoint163Value+41)=0 := by grind
  have hm := congrArg (fun x : ScalarAlgebra.Value => halfValue*x) ht
  grind

theorem cmPoint163_quadratic :
    (ComplexRaw.mul cmPoint163 cmPoint163).Equiv
      (integerAffine 1 (-41) cmPoint163) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.mul_valid cmPoint163_valid cmPoint163_valid)
    (hright := integerAffine_valid _ _ cmPoint163_valid)
  rw [ComplexRawQuotient.ofRaw_mul,
    integerAffine_class 1 (-41) (⟨cmPoint163,cmPoint163_valid⟩ : Scalar)]
  have h := cmPoint163Value_quadratic
  change cmPoint163Value*cmPoint163Value =
    ((1:Int):ScalarAlgebra.Value)*cmPoint163Value+((-41:Int):ScalarAlgebra.Value)
  grind

end ComputableAnalysis.ModularForms
