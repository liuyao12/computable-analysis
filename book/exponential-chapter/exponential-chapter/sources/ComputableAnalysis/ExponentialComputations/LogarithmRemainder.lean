import ComputableAnalysis.ModularForms.ExponentialLogarithmAgreement
import ComputableAnalysis.RiemannHilbert.GeneralSeriesDerivativeInitial

/-! Quantitative linearization of the constructed logarithm. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE

/-- The local logarithm differs from its linear term by a quadratic error,
for every valid represented complex input in its actual chart. -/
theorem localLogarithm_linear_error (z : Scalar)
    (hz : interior LocalLogarithm.radius.val z) (H : Rat) (hH : 0 ≤ H)
    (hsmall : Small z.val H) :
    Small (sub (LocalLogarithm.function.eval z hz).val z.val) (16*H^2) := by
  let L := LocalLogarithm.function.eval z hz
  let a : Scalar := ⟨zero,ofQComplex_valid _⟩
  have h0 := LocalLogarithm.initial
  have hd := BoundedSeries.sumDerivative_zero LocalLogarithm.coefficient
    LocalLogarithm.coefficient_valid 1 1 LocalLogarithm.radius.val
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    LocalLogarithm.coefficient_bound (by decide +kernel)
  have h1 : (LocalLogarithm.coefficient 1).Equiv one := by
    change (scaleRat (1/1) one).Equiv one
    rw [show (1:Rat)/1=1 by decide +kernel]
    exact scaleRat_one_equiv one (ofQComplex_valid _)
  have he0 : (sub z.val zero).Equiv z.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid z.property (ofQComplex_valid _)) (hright := z.property)
    change ComplexRawQuotient.ofRaw z.val z.property-0=ComplexRawQuotient.ofRaw z.val z.property
    grind only
  have hb := BoundedSeries.sum_remainder_bound LocalLogarithm.coefficient zero z.val
    LocalLogarithm.coefficient_valid (ofQComplex_valid _) z.property
    1 1 LocalLogarithm.radius.val H
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hH
    LocalLogarithm.coefficient_bound (Small.zero (by decide +kernel))
    (interior_bound _ z hz)
    (Small.congr z.property (sub_valid z.property (ofQComplex_valid _))
      (equiv_symm he0) hsmall) (by decide +kernel)
  have hD := equiv_trans
    (BoundedSeries.sumDerivative_valid LocalLogarithm.coefficient zero
      LocalLogarithm.coefficient_valid (ofQComplex_valid _) 1 1 LocalLogarithm.radius.val
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      LocalLogarithm.coefficient_bound (Small.zero (by decide +kernel)) (by decide +kernel))
    (LocalLogarithm.coefficient_valid 1) (ofQComplex_valid _) hd h1
  have hDv := BoundedSeries.sumDerivative_valid LocalLogarithm.coefficient zero
    LocalLogarithm.coefficient_valid (ofQComplex_valid _) 1 1 LocalLogarithm.radius.val
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    LocalLogarithm.coefficient_bound (Small.zero (by decide +kernel)) (by decide +kernel)
  have hm := mul_equiv hDv (ofQComplex_valid _) (sub_valid z.property (ofQComplex_valid _))
    z.property hD he0
  have hh := FunctionTheory.sub_congr
    (FunctionTheory.sub_congr (equiv_refl _ L.property) h0) hm
  have he2 : (sub (sub L.val zero) (mul one z.val)).Equiv (sub L.val z.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (sub_valid L.property (ofQComplex_valid _))
        (mul_valid (ofQComplex_valid _) z.property)) (hright := sub_valid L.property z.property)
    change (ComplexRawQuotient.ofRaw L.val L.property-0)-1*ComplexRawQuotient.ofRaw z.val z.property=
      ComplexRawQuotient.ofRaw L.val L.property-ComplexRawQuotient.ofRaw z.val z.property
    grind only
  have hvalid := SeriesLimitLaws.remainder_valid _ _ _ _ L.property
    (LocalLogarithm.function.eval a (interior_zero _ LocalLogarithm.radius.property)).property
    (BoundedSeries.sumDerivative_valid _ _ LocalLogarithm.coefficient_valid (ofQComplex_valid _)
      1 1 LocalLogarithm.radius.val (by decide +kernel) (by decide +kernel)
      (by decide +kernel) LocalLogarithm.coefficient_bound (Small.zero (by decide +kernel))
      (by decide +kernel)) (sub_valid z.property (ofQComplex_valid QComplex.zero))
  have he := equiv_trans hvalid
    (sub_valid (sub_valid L.property (ofQComplex_valid _))
      (mul_valid (ofQComplex_valid _) z.property)) (sub_valid L.property z.property) hh he2
  have hh := Small.congr hvalid (sub_valid L.property z.property) he hb
  rw [show (1:Rat)^2=1 by decide +kernel] at hh
  simpa only [Rat.mul_one] using hh
end ComputableAnalysis.ExponentialComputations
