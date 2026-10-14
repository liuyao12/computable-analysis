import ComputableAnalysis.ModularForms.PairedDivisionRationalCoefficientBounds

/-! Exact quadratic Riccati coefficient identity from actual shrinking rational samples. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def coefficientSampleRadius (eps : QPos) : QPos :=
  minRadius (minRadius (pairedDivisionCenterDerivativeRadius eps) ⟨1/8,by decide +kernel⟩) eps

private theorem coefficientDefect_small (eps : QPos) :
    Small pairedDivisionQuadraticCoefficientDefect.val (740354*eps.val) := by
  let r := coefficientSampleRadius eps
  have hr1 : r.val≤(1:Rat)/8 := Rat.le_trans (minRadius_left _ _) (minRadius_right _ _)
  have hre : r.val≤eps.val := minRadius_right _ _
  have hrd : r.val≤(pairedDivisionCenterDerivativeRadius eps).val :=
    Rat.le_trans (minRadius_left _ _) (minRadius_left _ _)
  have hr : r.val<(1:Rat)/4 := by
    have hsmall : (1:Rat)/8<(1:Rat)/4 := by decide +kernel
    grind only
  have h := pairedDivisionQuadraticCoefficientDefect_rational_bound eps r hr hrd
  have hr0 : 0≤r.val := Rat.le_of_lt r.property
  have hr2 : r.val*r.val≤eps.val := by
    have hmul := Rat.mul_le_mul_of_nonneg_right (Rat.le_trans hr1 (show (1:Rat)/8≤1 by decide +kernel)) hr0
    grind only
  apply h.mono
  have hm := Rat.mul_le_mul_of_nonneg_left hr2 (show (0:Rat)≤740352 by decide +kernel)
  grind only

/-- The actual quadratic Riccati coefficient vanishes exactly: five copies of
the constructed quadratic coefficient plus the square of its constant coefficient. -/
theorem pairedDivisionQuadraticCoefficientDefect_eq_zero :
    pairedDivisionQuadraticCoefficientDefect.val.Equiv zero := by
  have hs : Small pairedDivisionQuadraticCoefficientDefect.val 0 := by
    have he := SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks
      740354 (show (0:Rat)≤740354 by decide +kernel)
    apply SeriesLimitLaws.small_closed _ 0 _ he
    intro N
    simpa only [Rat.zero_add] using coefficientDefect_small (RepresentedCauchySum.error N)
  have he : (sub pairedDivisionQuadraticCoefficientDefect.val zero).Equiv
      pairedDivisionQuadraticCoefficientDefect.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid pairedDivisionQuadraticCoefficientDefect.property (ofQComplex_valid _))
      (hright := pairedDivisionQuadraticCoefficientDefect.property)
    change ComplexRawQuotient.ofRaw pairedDivisionQuadraticCoefficientDefect.val
      pairedDivisionQuadraticCoefficientDefect.property-0=
      ComplexRawQuotient.ofRaw pairedDivisionQuadraticCoefficientDefect.val pairedDivisionQuadraticCoefficientDefect.property
    grind only
  exact SeriesLimitLaws.equiv_of_small_sub_zero _ _
    (Small.congr pairedDivisionQuadraticCoefficientDefect.property
      (sub_valid pairedDivisionQuadraticCoefficientDefect.property (ofQComplex_valid _)) (equiv_symm he) hs)

/-- Exact evaluation of the constructed quadratic coefficient from its constant coefficient. -/
theorem pairedCenterQuadraticSum_center_square :
    pairedCenterQuadraticSum.Equiv
      (scaleRat (-1/5) (mul pairedCenterConstantSum pairedCenterConstantSum)) := by
  have hz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := pairedDivisionQuadraticCoefficientDefect.property) (hright := ofQComplex_valid _)
    pairedDivisionQuadraticCoefficientDefect_eq_zero
  let B := ComplexRawQuotient.ofRaw pairedCenterQuadraticSum pairedCenterQuadraticSum_valid
  let A := ComplexRawQuotient.ofRaw pairedCenterConstantSum pairedCenterConstantSum_valid
  change B+(B+(B+(B+(B+A*A))))=0 at hz
  have hfive : ComplexRawQuotient.scaleRat 5 B=B+(B+(B+(B+B))) := by
    have h := ScalarAlgebra.scale_natural 5 B
    rw [show ((5:Nat):Rat)=5 by decide +kernel] at h
    rw [h]
    grind only
  have hzero : ComplexRawQuotient.scaleRat 5 B+A*A=0 := by
    rw [hfive]
    grind only
  have h := congrArg (ComplexRawQuotient.scaleRat (-1/5)) hzero
  have hscale0 : ComplexRawQuotient.scaleRat (-1/5) (0:ScalarAlgebra.Value)=0 :=
    ComplexRawQuotient.scaleRat_zero (-1/5)
  rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.scaleRat_scaleRat,
    hscale0,show (-1/5:Rat)*5= -1 by decide +kernel,
    ← ComplexRawQuotient.neg_eq_scaleRat_neg_one] at h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := pairedCenterQuadraticSum_valid)
    (hright := scaleRat_valid (mul_valid pairedCenterConstantSum_valid pairedCenterConstantSum_valid))
  change B=ComplexRawQuotient.scaleRat (-1/5) (A*A)
  generalize ComplexRawQuotient.scaleRat (-1/5) (A*A)=C at h ⊢
  grind only

end ComputableAnalysis.ModularForms
