import ComputableAnalysis.ModularForms.LatticeHalfPeriodZero
import ComputableAnalysis.ModularForms.NomePoleRegularization
import ComputableAnalysis.ModularForms.ExponentialHalfPeriod

/-! Exact nome phase at the represented half-period. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem nomeHalfPeriod_exponent :
    ((affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval latticeHalfPoint trivial).val.Equiv
      imaginaryPiScalar.val := by
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := scaleRat_valid (r := 1/2) (ofQComplex_valid _))
    (hright := latticeHalfPoint.property) (rationalScalarOne_equiv (1/2))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval latticeHalfPoint trivial).property)
    (hright := imaginaryPiScalar.property)
  let B := ComplexRawQuotient.ofRaw GeometricPiRotation.imaginaryHalf GeometricPiRotation.imaginaryHalf_valid
  let H := gridScalarValue latticeHalfPoint
  change ComplexRawQuotient.scaleRat (1/2) 1=H at hh
  change 0+ComplexRawQuotient.scaleRat 4 B*H=ComplexRawQuotient.scaleRat 2 B
  rw [←hh,ComplexRawQuotient.mul_scaleRat,←ComplexRawQuotient.scaleRat_mul,
    ComplexRawQuotient.scaleRat_scaleRat]
  have hc : (1/2:Rat)*4=2 := by decide +kernel
  rw [hc]
  grind only

theorem entireNomeMap_halfPeriod :
    (entireNomeMap.eval latticeHalfPoint (entireNomeMap_mem latticeHalfPoint)).val.Equiv
      (ofQComplex ⟨-1,0⟩) :=
  equiv_trans (entireNomeMap.eval latticeHalfPoint (entireNomeMap_mem latticeHalfPoint)).property
    (entireExponentialValue imaginaryPiScalar).property (ofQComplex_valid _)
    (entireExponentialValue_congr _ _ nomeHalfPeriod_exponent) entireExponential_imaginaryPi

def entireNomeCotangentMap : DomainFunctions.Map := compose cotangentRationalMap entireNomeMap

def entireNomeCotangentMap_holomorphic : Holomorphic entireNomeCotangentMap :=
  cotangentRationalMap_holomorphic.compose entireNomeMap_holomorphic

theorem entireNomeCotangent_halfPeriod_mem : entireNomeCotangentMap.domain latticeHalfPoint := by
  let q := entireNomeMap.eval latticeHalfPoint (entireNomeMap_mem latticeHalfPoint)
  have hq := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property)
    (hright := ofQComplex_valid _) entireNomeMap_halfPeriod
  have hi : (mul (nomeDenominator q).val latticeHalfPoint.val).Equiv (ofQComplex QComplex.one) := by
    have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := scaleRat_valid (r := 1/2) (ofQComplex_valid _))
      (hright := latticeHalfPoint.property) (rationalScalarOne_equiv (1/2))
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid (nomeDenominator q).property latticeHalfPoint.property)
      (hright := ofQComplex_valid _)
    let Q := gridScalarValue q
    let H := gridScalarValue latticeHalfPoint
    change Q= -1 at hq
    change ComplexRawQuotient.scaleRat (1/2) 1=H at hh
    change (1-Q)*H=1
    rw [hq,←hh,ComplexRawQuotient.mul_scaleRat]
    have he : (1-(-1:ScalarAlgebra.Value))*1=ComplexRawQuotient.scaleRat 2 1 := by
      rw [gridValue_scale_two]
      grind only
    rw [he,ComplexRawQuotient.scaleRat_scaleRat]
    have hc : (1/2:Rat)*2=1 := by decide +kernel
    rw [hc,ComplexRawQuotient.scaleRat_one]
  exact ⟨entireNomeMap_mem latticeHalfPoint,(cotangentRationalMap_domain q).mpr
    (RepresentedReciprocal.nonzero_of_inverse (nomeDenominator q) latticeHalfPoint hi)⟩

theorem entireNomeCotangent_halfPeriod_zero :
    (entireNomeCotangentMap.eval latticeHalfPoint entireNomeCotangent_halfPeriod_mem).val.Equiv zero := by
  let hz := entireNomeCotangent_halfPeriod_mem
  let q := entireNomeMap.eval latticeHalfPoint (compose_inner_mem hz)
  let hq := compose_outer_mem hz
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property)
    (hright := ofQComplex_valid _) entireNomeMap_halfPeriod
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (entireNomeCotangentMap.eval latticeHalfPoint hz).property) (hright := ofQComplex_valid _)
  let Q := gridScalarValue q
  let J := gridScalarValue (nomeRationalInverseMap.eval q hq)
  change Q= -1 at he
  change J*(1+1*Q)=(0:ScalarAlgebra.Value)
  rw [he]
  grind only

end ComputableAnalysis.ModularForms
