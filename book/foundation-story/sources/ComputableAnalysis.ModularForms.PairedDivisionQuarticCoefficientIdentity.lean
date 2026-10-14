import ComputableAnalysis.ModularForms.PairedDivisionQuarticCoefficientDefect

/-! Exact quartic coefficient identity from shrinking actual rational samples. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

/-- Two justified rational-square cancellations remove the fourth power of the sample. -/
theorem rationalReal_fourth_cancel_small (E : Scalar) (r : QPos) (L : Rat)
    (h : Small (mul (mul (mul (pairedCoefficientRationalSample r).val (pairedCoefficientRationalSample r).val)
      (mul (pairedCoefficientRationalSample r).val (pairedCoefficientRationalSample r).val)) E.val) L) :
    Small E.val ((r.val*r.val)⁻¹*((r.val*r.val)⁻¹*L)) := by
  let z := pairedCoefficientRationalSample r
  let z2 := scalarProduct z z
  let p := scalarProduct z2 E
  have he : (mul (mul z2.val z2.val) E.val).Equiv (mul z2.val p.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := mul_valid (mul_valid z2.property z2.property) E.property)
      (hright := mul_valid z2.property p.property)
    let Z := ComplexRawQuotient.ofRaw z2.val z2.property
    let C := ComplexRawQuotient.ofRaw E.val E.property
    change (Z*Z)*C=Z*(Z*C)
    grind only
  have hs := Small.congr (mul_valid (mul_valid z2.property z2.property) E.property)
    (mul_valid z2.property p.property) he h
  have hp := rationalReal_square_cancel_small p r L hs
  exact rationalReal_square_cancel_small E r ((r.val*r.val)⁻¹*L) hp

/-- The actual quartic coefficient defect has a quadratic bound at every positive rational sample in the disk. -/
theorem pairedDivisionQuarticCoefficientDefect_rational_bound (r : QPos) (hr : r.val<(1:Rat)/4) :
    Small pairedDivisionQuarticCoefficientDefect.val (307200*r.val*r.val) := by
  have hz := pairedCoefficientRationalSample_interior r hr
  have h := pairedDivisionQuarticCoefficientDefect_scaled_bound (pairedCoefficientRationalSample r) hz r.val
    (Rat.le_of_lt r.property) (pairedCoefficientRationalSample_small r)
  have hc := rationalReal_fourth_cancel_small pairedDivisionQuarticCoefficientDefect r _ h
  have hi : (r.val*r.val)⁻¹*(r.val*r.val)=1 :=
    Rat.inv_mul_cancel (r.val*r.val) (Rat.ne_of_gt (Rat.mul_pos r.property r.property))
  have he : (r.val*r.val)⁻¹*((r.val*r.val)⁻¹*(307200*r.val*r.val*r.val*r.val*r.val*r.val))=
      307200*r.val*r.val := by
    generalize (r.val*r.val)⁻¹=M at hi ⊢
    grind only
  rw [he] at hc
  exact hc

private theorem coefficient_small (eps : QPos) :
    Small pairedDivisionQuarticCoefficientDefect.val (307200*eps.val) := by
  let r := minRadius (⟨1/8,by decide +kernel⟩ : QPos) eps
  have hr1 : r.val≤(1:Rat)/8 := minRadius_left _ _
  have hre : r.val≤eps.val := minRadius_right _ _
  have hr : r.val<(1:Rat)/4 := by
    have h : (1:Rat)/8<(1:Rat)/4 := by decide +kernel
    grind only
  have h := pairedDivisionQuarticCoefficientDefect_rational_bound r hr
  have hr0 : 0≤r.val := Rat.le_of_lt r.property
  have hr2 : r.val*r.val≤eps.val := by
    have hmul := Rat.mul_le_mul_of_nonneg_right (Rat.le_trans hr1 (show (1:Rat)/8≤1 by decide +kernel)) hr0
    grind only
  apply h.mono
  have hm := Rat.mul_le_mul_of_nonneg_left hr2 (show (0:Rat)≤307200 by decide +kernel)
  grind only

/-- The actual quartic Riccati coefficient vanishes exactly. -/
theorem pairedDivisionQuarticCoefficientDefect_eq_zero :
    pairedDivisionQuarticCoefficientDefect.val.Equiv zero := by
  have hs : Small pairedDivisionQuarticCoefficientDefect.val 0 := by
    have he := SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks
      307200 (show (0:Rat)≤307200 by decide +kernel)
    apply SeriesLimitLaws.small_closed _ 0 _ he
    intro N
    simpa only [Rat.zero_add] using coefficient_small (RepresentedCauchySum.error N)
  have he : (sub pairedDivisionQuarticCoefficientDefect.val zero).Equiv pairedDivisionQuarticCoefficientDefect.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid pairedDivisionQuarticCoefficientDefect.property (ofQComplex_valid _))
      (hright := pairedDivisionQuarticCoefficientDefect.property)
    change ComplexRawQuotient.ofRaw pairedDivisionQuarticCoefficientDefect.val pairedDivisionQuarticCoefficientDefect.property-0=
      ComplexRawQuotient.ofRaw pairedDivisionQuarticCoefficientDefect.val pairedDivisionQuarticCoefficientDefect.property
    grind only
  exact SeriesLimitLaws.equiv_of_small_sub_zero _ _
    (Small.congr pairedDivisionQuarticCoefficientDefect.property
      (sub_valid pairedDivisionQuarticCoefficientDefect.property (ofQComplex_valid _)) (equiv_symm he) hs)

/-- Exact evaluation of the constructed quartic coefficient from the lower coefficients. -/
theorem pairedCenterQuarticSum_center_product :
    pairedCenterQuarticSum.Equiv (scaleRat (-2/7) (mul pairedCenterConstantSum pairedCenterQuadraticSum)) := by
  have hz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := pairedDivisionQuarticCoefficientDefect.property) (hright := ofQComplex_valid _)
    pairedDivisionQuarticCoefficientDefect_eq_zero
  let D := ComplexRawQuotient.ofRaw pairedCenterQuarticSum pairedCenterQuarticSum_valid
  let A := ComplexRawQuotient.ofRaw pairedCenterConstantSum pairedCenterConstantSum_valid
  let B := ComplexRawQuotient.ofRaw pairedCenterQuadraticSum pairedCenterQuadraticSum_valid
  change ComplexRawQuotient.scaleRat 7 D+ComplexRawQuotient.scaleRat 2 (A*B)=0 at hz
  have h := congrArg (ComplexRawQuotient.scaleRat (-1/7)) hz
  have hscale0 : ComplexRawQuotient.scaleRat (-1/7) (0:ScalarAlgebra.Value)=0 :=
    ComplexRawQuotient.scaleRat_zero (-1/7)
  rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.scaleRat_scaleRat,
    ComplexRawQuotient.scaleRat_scaleRat,hscale0,
    show (-1/7:Rat)*7= -1 by decide +kernel,
    show (-1/7:Rat)*2= -2/7 by decide +kernel,
    ← ComplexRawQuotient.neg_eq_scaleRat_neg_one] at h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := pairedCenterQuarticSum_valid)
    (hright := scaleRat_valid (mul_valid pairedCenterConstantSum_valid pairedCenterQuadraticSum_valid))
  change D=ComplexRawQuotient.scaleRat (-2/7) (A*B)
  generalize ComplexRawQuotient.scaleRat (-2/7) (A*B)=C at h ⊢
  grind only

end ComputableAnalysis.ModularForms
