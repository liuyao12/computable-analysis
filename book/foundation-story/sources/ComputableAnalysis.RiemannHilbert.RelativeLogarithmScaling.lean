import ComputableAnalysis.RiemannHilbert.RadialLogarithmChains

/-! Exact invariance of relative logarithms under simultaneous positive
rational dilation. This includes the actual recursively chosen radial
centers and arbitrary valid represented endpoint names. -/
namespace ComputableAnalysis.RiemannHilbert.RelativeLogarithmScaling
open ComplexRaw FunctionTheory DomainFunctions NonzeroBoxSearch RadialLogarithmChains
set_option autoImplicit false

theorem inverse_scale (r : Rat) (hr : 0 < r) (c : Scalar) (hc : Nonzero c) :
    (RepresentedReciprocal.inverse (scale r c) (scale_nonzero r hr c hc)).val.Equiv
      (scale r⁻¹ (RepresentedReciprocal.inverse c hc)).val := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid c.property (RepresentedReciprocal.inverse c hc).property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse c hc)
  apply RepresentedReciprocal.inverse_unique
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (scale r c).property (scale r⁻¹ (RepresentedReciprocal.inverse c hc)).property)
    (hright := ofQComplex_valid _)
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  change C*I=1 at hi
  change ComplexRawQuotient.scaleRat r C*ComplexRawQuotient.scaleRat r⁻¹ I=1
  rw [ComplexRawQuotient.scaleRat_mul_scaleRat,hi,Rat.mul_inv_cancel r (Rat.ne_of_gt hr),ComplexRawQuotient.scaleRat_one]

theorem point_scale (r : Rat) (hr : 0 < r) (c : Scalar) (hc : Nonzero c) (z : Scalar) :
    (RelativeLogarithm.point (scale r c) (scale_nonzero r hr c hc) (scale r z)).val.Equiv
      (RelativeLogarithm.point c hc z).val := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (RepresentedReciprocal.inverse (scale r c) (scale_nonzero r hr c hc)).property)
    (hright := (scale r⁻¹ (RepresentedReciprocal.inverse c hc)).property) (inverse_scale r hr c hc)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (RelativeLogarithm.point (scale r c) (scale_nonzero r hr c hc) (scale r z)).property)
    (hright := (RelativeLogarithm.point c hc z).property)
  let S := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse (scale r c) (scale_nonzero r hr c hc)).val
    (RepresentedReciprocal.inverse (scale r c) (scale_nonzero r hr c hc)).property
  let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse c hc).val (RepresentedReciprocal.inverse c hc).property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change S=ComplexRawQuotient.scaleRat r⁻¹ I at he
  change -1+S*ComplexRawQuotient.scaleRat r Z = -1+I*Z
  rw [he,ComplexRawQuotient.scaleRat_mul_scaleRat,Rat.inv_mul_cancel r (Rat.ne_of_gt hr),ComplexRawQuotient.scaleRat_one]

theorem domain_scale (r : Rat) (hr : 0 < r) (c : Scalar) (hc : Nonzero c) (z : Scalar) :
    RelativeLogarithm.domain (scale r c) (scale_nonzero r hr c hc) (scale r z) ↔ RelativeLogarithm.domain c hc z :=
  LocalLogarithm.function.domain_congr _ _ (point_scale r hr c hc z)

theorem value_scale (r : Rat) (hr : 0 < r) (c : Scalar) (hc : Nonzero c) (z : Scalar)
    (hs : RelativeLogarithm.domain (scale r c) (scale_nonzero r hr c hc) (scale r z))
    (hz : RelativeLogarithm.domain c hc z) :
    ((RelativeLogarithm.function (scale r c) (scale_nonzero r hr c hc)).eval (scale r z) hs).val.Equiv
      ((RelativeLogarithm.function c hc).eval z hz).val :=
  LocalLogarithm.function.eval_congr _ _ hs hz (point_scale r hr c hc z)

theorem radial_point (c d : Scalar) (hc : Nonzero c) (k : Nat) :
    (RelativeLogarithm.point (RadialLogarithmChains.center c k) (center_nonzero c hc k) (RadialLogarithmChains.center d k)).val.Equiv
      (RelativeLogarithm.point c hc d).val := by
  let r := RadialGrowthArithmetic.ratio^k
  have hr : 0 < r := Rat.pow_pos RadialGrowthArithmetic.ratio_positive
  let hsc := scale_nonzero r hr c hc
  exact equiv_trans (RelativeLogarithm.point (RadialLogarithmChains.center c k) (center_nonzero c hc k) (RadialLogarithmChains.center d k)).property
    (RelativeLogarithm.point (scale r c) hsc (scale r d)).property (RelativeLogarithm.point c hc d).property
    (RelativeLogarithm.point_congr (RadialLogarithmChains.center c k) (scale r c) (center_nonzero c hc k) hsc
      (center_value c k) (RadialLogarithmChains.center d k) (scale r d) (center_value d k))
    (point_scale r hr c hc d)

theorem radial_domain (c d : Scalar) (hc : Nonzero c) (k : Nat) :
    RelativeLogarithm.domain (RadialLogarithmChains.center c k) (center_nonzero c hc k) (RadialLogarithmChains.center d k) ↔
      RelativeLogarithm.domain c hc d := LocalLogarithm.function.domain_congr _ _ (radial_point c d hc k)

theorem radial_value (c d : Scalar) (hc : Nonzero c) (k : Nat)
    (hk : RelativeLogarithm.domain (RadialLogarithmChains.center c k) (center_nonzero c hc k) (RadialLogarithmChains.center d k))
    (hcd : RelativeLogarithm.domain c hc d) :
    ((RelativeLogarithm.function (RadialLogarithmChains.center c k) (center_nonzero c hc k)).eval (RadialLogarithmChains.center d k) hk).val.Equiv
      ((RelativeLogarithm.function c hc).eval d hcd).val :=
  LocalLogarithm.function.eval_congr _ _ hk hcd (radial_point c d hc k)

end ComputableAnalysis.RiemannHilbert.RelativeLogarithmScaling
