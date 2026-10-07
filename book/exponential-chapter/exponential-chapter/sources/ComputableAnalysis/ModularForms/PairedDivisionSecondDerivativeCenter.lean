import ComputableAnalysis.ModularForms.PairedDivisionSecondDerivative
import ComputableAnalysis.ModularForms.PairedDivisionFirstDerivativeHolomorphic
import ComputableAnalysis.ModularForms.PairedRegularDivisionZeroSum

/-! Actual inverse-fourth coefficients of regular division at the lattice center. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedZeroFourthTerm (n : Nat) : ComplexRaw :=
  scaleRat (-4) (ofQComplex ⟨reciprocalSquare (n+1)*reciprocalSquare (n+1),0⟩)

/-- The actual second-derivative term at zero is the inverse-fourth coefficient. -/
theorem pairedDivisionSecondDerivativeTerm_at_zero (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (he : z.val.Equiv zero) (n : Nat) :
    (pairedDivisionSecondDerivativeTerm z hz n).val.Equiv (pairedZeroFourthTerm n) := by
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let c := reciprocalSquare (n+1)
  have hi := pairedSmallDiskLiteralInverse_at_zero z hz he n
  have hprod := mul_equiv i.property (ofQComplex_valid _) i.property (ofQComplex_valid _) hi hi
  have hrat := rationalRealProduct_equiv (-c) (-c)
  have hc : (-c)*(-c)=c*c := by grind only
  rw [hc] at hrat
  have hsq := equiv_trans (mul_valid i.property i.property)
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _) hprod hrat
  have hZ := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := ofQComplex_valid _) he
  have hI := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid i.property i.property)
    (hright := ofQComplex_valid _) hsq
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (pairedDivisionSecondDerivativeTerm z hz n).property)
    (hright := scaleRat_valid (ofQComplex_valid _))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let I := ComplexRawQuotient.ofRaw i.val i.property
  let A := ComplexRawQuotient.ofRaw (ofQComplex ⟨c*c,0⟩) (ofQComplex_valid _)
  change Z=0 at hZ
  change I*I=A at hI
  change ((-(I*I)+-(I*I))+(-(I*I)+-(I*I)))+
    (((((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))+((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I))))+
      (((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))+((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))))+
     ((((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))+((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I))))+
      (((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I)))+((Z*Z)*(I*(I*I))+(Z*Z)*(I*(I*I))))))=
    ComplexRawQuotient.scaleRat (-4) A
  rw [hZ]
  rw [hI]
  simp only [ComplexRawQuotient.neg_eq_scaleRat_neg_one]
  simp only [ComplexRawQuotient.add_scaleRat]
  have hzero : (0:ScalarAlgebra.Value)*0*(I*A)=0 := by grind only
  rw [hzero]
  have hfour : (-1:Rat)+ -1+(-1+ -1)= -4 := by decide +kernel
  rw [hfour]
  grind only

theorem pairedZeroFourthTerm_valid (n : Nat) : (pairedZeroFourthTerm n).Valid :=
  scaleRat_valid (ofQComplex_valid _)

theorem pairedZeroFourthTerm_bound (n : Nat) :
    Small (pairedZeroFourthTerm n) (1152*reciprocalSquare (n+1)) :=
  Small.congr (pairedDivisionSecondDerivativeTerm pairedZeroScalar pairedZeroScalar_interior n).property
    (pairedZeroFourthTerm_valid n)
    (pairedDivisionSecondDerivativeTerm_at_zero pairedZeroScalar pairedZeroScalar_interior
      (equiv_refl _ pairedZeroScalar.property) n)
    (pairedDivisionSecondDerivativeTerm_bound pairedZeroScalar pairedZeroScalar_interior n)

def pairedZeroFourthSum : ComplexRaw :=
  inverseSquareSeriesValue pairedZeroFourthTerm pairedZeroFourthTerm_valid 1152

theorem pairedZeroFourthSum_valid : pairedZeroFourthSum.Valid :=
  inverseSquareSeriesValue_valid _ _ 1152 pairedZeroFourthTerm_bound

theorem pairedZeroFourthSum_close (N : Nat) :
    Small (sub pairedZeroFourthSum (ScalarSeries.block pairedZeroFourthTerm 0 (N+1)))
      (1152*((N+1:Nat):Rat)⁻¹) :=
  inverseSquareSeriesValue_close _ _ 1152 pairedZeroFourthTerm_bound N

/-- Exact center evaluation of the constructed second-derivative series. -/
theorem pairedDivisionSecondDerivativeValue_at_zero (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (he : z.val.Equiv zero) :
    (pairedDivisionSecondDerivativeValue z hz).Equiv pairedZeroFourthSum :=
  inverseSquareSeriesValue_congr _ _ (fun n => (pairedDivisionSecondDerivativeTerm z hz n).property)
    pairedZeroFourthTerm_valid 1152 (pairedDivisionSecondDerivativeTerm_bound z hz)
    pairedZeroFourthTerm_bound (pairedDivisionSecondDerivativeTerm_at_zero z hz he)

/-- The proved holomorphic second derivative at the center has this same value. -/
theorem pairedDivisionFirstDerivativeMap_derivative_at_zero (z : Scalar)
    (hz : pairedDivisionFirstDerivativeMap.domain z) (he : z.val.Equiv zero) :
    (pairedDivisionFirstDerivativeMap_holomorphic.derivative z hz).val.Equiv pairedZeroFourthSum :=
  pairedDivisionSecondDerivativeValue_at_zero z hz he

end ComputableAnalysis.ModularForms
