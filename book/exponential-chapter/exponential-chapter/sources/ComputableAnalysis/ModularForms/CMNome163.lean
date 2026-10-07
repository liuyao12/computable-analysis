import ComputableAnalysis.ModularForms.ExponentialInverse
import ComputableAnalysis.ModularForms.ExponentialHalfPeriod
import ComputableAnalysis.ModularForms.CMEquation163
import ComputableAnalysis.ModularForms.UpperLatticeCM163Agreement
import ComputableAnalysis.ModularForms.Nome

/-! The actual discriminant-163 nome is a negative real exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def geometricHalfPiRealScalar : Scalar :=
  ⟨ofRealRaw GeometricPiRotation.halfPi,ofRealRaw_valid _ GeometricPiRotation.halfPi_valid⟩

/-- The exponent representing minus pi times sqrt(163). -/
def cmDecayExponent163 : Scalar :=
  ⟨neg (scaleRat 2 (mul geometricHalfPiRealScalar.val sqrt163Complex)),
    neg_valid (scaleRat_valid (mul_valid geometricHalfPiRealScalar.property sqrt163Complex_valid))⟩

theorem cmNomeExponent163_decomposition :
    (nomeExponentMap.eval cmScalar163 cmPoint163_upper).val.Equiv
      (add cmDecayExponent163.val imaginaryPiScalar.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (nomeExponentMap.eval cmScalar163 cmPoint163_upper).property)
    (hright := add_valid cmDecayExponent163.property imaginaryPiScalar.property)
  let p := ComplexRawQuotient.ofRaw geometricHalfPiRealScalar.val geometricHalfPiRealScalar.property
  let r := sqrt163Value
  let i := imaginaryUnitValue
  have hi := mulI_class geometricHalfPiRealScalar
  have hcm := cmPoint163Value_formula
  change ComplexRawQuotient.ofRaw cmPoint163 cmPoint163_valid =
    ComplexRawQuotient.scaleRat (1/2) (1+i*r) at hcm
  change ComplexRawQuotient.scaleRat 4
    (ComplexRawQuotient.ofRaw (mulI geometricHalfPiRealScalar.val)
      (mulI_valid geometricHalfPiRealScalar.property)) *
    ComplexRawQuotient.ofRaw cmPoint163 cmPoint163_valid =
    -ComplexRawQuotient.scaleRat 2 (p*r) +
    ComplexRawQuotient.scaleRat 2
      (ComplexRawQuotient.ofRaw (mulI geometricHalfPiRealScalar.val)
        (mulI_valid geometricHalfPiRealScalar.property))
  rw [hi,hcm,ComplexRawQuotient.mul_scaleRat,← ComplexRawQuotient.scaleRat_mul,
    ComplexRawQuotient.scaleRat_scaleRat]
  have hc : (1/2:Rat)*4=2 := by decide +kernel
  rw [hc]
  have h2 (v : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 v=(2:ScalarAlgebra.Value)*v :=
    ScalarAlgebra.scale_natural 2 v
  rw [h2,h2,h2]
  have hs := imaginaryUnitValue_square
  have hneg : (((-1):Int):ScalarAlgebra.Value) = -(1:ScalarAlgebra.Value) := by
    grind only
  rw [hneg] at hs
  grind only

theorem nome_cm163_negative_exponential :
    (nome.eval cmScalar163 cmPoint163_upper).val.Equiv
      (neg (entireExponentialValue cmDecayExponent163).val) := by
  let x : Scalar := ⟨add cmDecayExponent163.val imaginaryPiScalar.val,
    add_valid cmDecayExponent163.property imaginaryPiScalar.property⟩
  exact equiv_trans (nome.eval cmScalar163 cmPoint163_upper).property
    (entireExponentialValue x).property (neg_valid (entireExponentialValue cmDecayExponent163).property)
    (entireExponentialValue_congr _ x cmNomeExponent163_decomposition)
    (entireExponential_add_imaginaryPi cmDecayExponent163)

/-- The corresponding exponent representing pi times sqrt(163). -/
def cmGrowthExponent163 : Scalar :=
  ⟨neg cmDecayExponent163.val,neg_valid cmDecayExponent163.property⟩

theorem nome_cm163_growth_product :
    (mul (nome.eval cmScalar163 cmPoint163_upper).val
      (entireExponentialValue cmGrowthExponent163).val).Equiv (ofQComplex ⟨-1,0⟩) := by
  have hn := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (nome.eval cmScalar163 cmPoint163_upper).property)
    (hright := neg_valid (entireExponentialValue cmDecayExponent163).property) nome_cm163_negative_exponential
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue cmDecayExponent163).property
      (entireExponentialValue cmGrowthExponent163).property) (hright := ofQComplex_valid _)
    (entireExponential_inverse cmDecayExponent163)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (nome.eval cmScalar163 cmPoint163_upper).property
      (entireExponentialValue cmGrowthExponent163).property) (hright := ofQComplex_valid _)
  let d := ComplexRawQuotient.ofRaw (entireExponentialValue cmDecayExponent163).val
    (entireExponentialValue cmDecayExponent163).property
  let g := ComplexRawQuotient.ofRaw (entireExponentialValue cmGrowthExponent163).val
    (entireExponentialValue cmGrowthExponent163).property
  change ComplexRawQuotient.ofRaw (nome.eval cmScalar163 cmPoint163_upper).val
    (nome.eval cmScalar163 cmPoint163_upper).property = -d at hn
  change d*g=1 at hi
  change ComplexRawQuotient.ofRaw (nome.eval cmScalar163 cmPoint163_upper).val
    (nome.eval cmScalar163 cmPoint163_upper).property *g = ComplexRawQuotient.ofQComplex ⟨-1,0⟩
  have hc : ComplexRawQuotient.ofQComplex ⟨-1,0⟩ = -(1:ScalarAlgebra.Value) := rfl
  rw [hn,hc]
  grind only

end ComputableAnalysis.ModularForms
