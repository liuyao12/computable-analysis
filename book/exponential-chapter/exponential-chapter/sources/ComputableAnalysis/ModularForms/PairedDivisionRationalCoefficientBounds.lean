import ComputableAnalysis.ModularForms.PairedDivisionCoefficientBounds
import ComputableAnalysis.ModularForms.RationalRealScaling

/-! Cancellation of the nonzero rational sample square in actual coefficient estimates. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedCoefficientRationalSample (r : QPos) : Scalar := ⟨ofQComplex ⟨r.val,0⟩,ofQComplex_valid _⟩

theorem pairedCoefficientRationalSample_small (r : QPos) :
    Small (pairedCoefficientRationalSample r).val r.val := by
  refine ⟨?_,?_,?_,?_⟩
  · intro a b
    change -r.val≤r.val
    have h := r.property
    grind only
  · intro a b
    exact Rat.le_refl
  · intro a b
    change -r.val≤0
    have h := r.property
    grind only
  · intro a b
    exact Rat.le_of_lt r.property

theorem pairedCoefficientRationalSample_interior (r : QPos) (hr : r.val<(1:Rat)/4) :
    LocalODE.interior (1/4) (pairedCoefficientRationalSample r) :=
  ⟨r.val,Rat.le_of_lt r.property,hr,pairedCoefficientRationalSample_small r⟩

/-- Exact rational-square cancellation transports an actual coefficient bound. -/
theorem rationalReal_square_cancel_small (E : Scalar) (r : QPos) (L : Rat)
    (h : Small (mul (mul (pairedCoefficientRationalSample r).val (pairedCoefficientRationalSample r).val) E.val) L) :
    Small E.val ((r.val*r.val)⁻¹*L) := by
  let z := pairedCoefficientRationalSample r
  have hp := rationalRealProduct_equiv r.val r.val
  have hm := mul_equiv (mul_valid z.property z.property) (ofQComplex_valid _) E.property E.property
    hp (equiv_refl E.val E.property)
  have he := equiv_trans (mul_valid (mul_valid z.property z.property) E.property)
    (mul_valid (ofQComplex_valid _) E.property) (scaleRat_valid E.property) hm
    (rationalReal_mul_scale (r.val*r.val) E)
  have hs := Small.congr (mul_valid (mul_valid z.property z.property) E.property) (scaleRat_valid E.property) he h
  have hpos := Rat.mul_pos r.property r.property
  have hi := LocalODE.small_scale (Rat.le_of_lt (Rat.inv_pos.mpr hpos)) hs
  have hcancel : (scaleRat ((r.val*r.val)⁻¹) (scaleRat (r.val*r.val) E.val)).Equiv E.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (scaleRat_valid E.property)) (hright := E.property)
    change ComplexRawQuotient.scaleRat ((r.val*r.val)⁻¹)
      (ComplexRawQuotient.scaleRat (r.val*r.val) (ComplexRawQuotient.ofRaw E.val E.property))=
      ComplexRawQuotient.ofRaw E.val E.property
    rw [ComplexRawQuotient.scaleRat_scaleRat,Rat.inv_mul_cancel (r.val*r.val) (Rat.ne_of_gt hpos),ComplexRawQuotient.scaleRat_one]
  exact Small.congr (scaleRat_valid (scaleRat_valid E.property)) E.property hcancel hi

/-- The actual quadratic coefficient has an unscaled bound at each admissible
nonzero rational sample. -/
theorem pairedDivisionQuadraticCoefficientDefect_rational_bound (eps r : QPos)
    (hr : r.val<(1:Rat)/4) (hlocal : r.val≤(pairedDivisionCenterDerivativeRadius eps).val) :
    Small pairedDivisionQuadraticCoefficientDefect.val (2*eps.val+740352*r.val*r.val) := by
  let z := pairedCoefficientRationalSample r
  have hz := pairedCoefficientRationalSample_interior r hr
  have h := pairedDivisionQuadraticCoefficientDefect_scaled_bound eps r z hz hlocal (pairedCoefficientRationalSample_small r)
  have hc := rationalReal_square_cancel_small pairedDivisionQuadraticCoefficientDefect r _ h
  have hi : (r.val*r.val)⁻¹*(r.val*r.val)=1 := Rat.inv_mul_cancel (r.val*r.val) (Rat.ne_of_gt (Rat.mul_pos r.property r.property))
  have he : (r.val*r.val)⁻¹*(2*eps.val*r.val*r.val+740352*r.val*r.val*r.val*r.val)=
      2*eps.val+740352*r.val*r.val := by
    generalize (r.val*r.val)⁻¹=M at hi ⊢
    grind only
  rw [he] at hc
  exact hc

end ComputableAnalysis.ModularForms
