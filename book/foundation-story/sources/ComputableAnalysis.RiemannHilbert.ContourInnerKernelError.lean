import ComputableAnalysis.RiemannHilbert.ContourFrameSampleValues

/-! The actual inner Cauchy sum differs from the center value times the
actual reciprocal sum by a mesh-independent, proved numerator error. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def cauchyInnerPrefix (f : DomainFunctions.Map) (a : Scalar) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) (M : Nat) : Scalar :=
  innerBoundary (cauchyFrameSample f a R hdom) R M

def reciprocalInnerPrefix (R : QPos) (M : Nat) : Scalar :=
  innerBoundary (reciprocalFrameSample R) R M

theorem centerErrorBoundary_identity (f : DomainFunctions.Map) (a : Scalar) (ha : f.domain a) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) (M : Nat) :
    innerBoundary (centerErrorSample f a ha R hdom) R M ≈
      gridScalarSub (cauchyInnerPrefix f a R hdom M) (scalarProduct (f.eval a ha) (reciprocalInnerPrefix R M)) := by
  let K := cauchyInnerPrefix f a R hdom M
  let P := reciprocalInnerPrefix R M
  let A := f.eval a ha
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (innerBoundary (centerErrorSample f a ha R hdom) R M).property)
    (hright := (scalarSum (scalarProduct oneScalar K) (scalarProduct (scalarNeg A) P)).property)
    (innerBoundary_linear oneScalar (scalarNeg A) (cauchyFrameSample f a R hdom) (reciprocalFrameSample R) R M)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (innerBoundary (centerErrorSample f a ha R hdom) R M).property)
    (hright := (gridScalarSub K (scalarProduct A P)).property)
  change gridScalarValue (innerBoundary (centerErrorSample f a ha R hdom) R M)=
    1*gridScalarValue K+(-gridScalarValue A)*gridScalarValue P at he
  change gridScalarValue (innerBoundary (centerErrorSample f a ha R hdom) R M)=
    gridScalarValue K-gridScalarValue A*gridScalarValue P
  grind only

theorem centerErrorSample_bound (f : DomainFunctions.Map) (a : Scalar) (ha : f.domain a) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) (eps : QPos)
    (hclose : ∀ z hz, Small (sub (f.eval (Centered.translate a z) (hdom z hz)).val (f.eval a ha).val) eps.val)
    (q : QComplex) (hq : frameDomain R (rationalRectangleScalar q)) :
    Small (centerErrorSample f a ha R hdom q).val (4*eps.val/R.val) := by
  let F := f.eval (Centered.translate a (rationalRectangleScalar q)) (hdom _ hq)
  let A := f.eval a ha
  let V := RepresentedReciprocal.inverse (rationalRectangleScalar q) (frameDomain_nonzero R _ hq)
  have hv : 0≤2/R.val := by
    rw [Rat.div_def]; exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr R.property))
  have hb := Small.mul (sub_valid F.property A.property) V.property
    (Rat.le_of_lt eps.property) hv (hclose _ hq) (frame_rational_inverse_bound R q hq _)
  have he : 2*eps.val*(2/R.val)=4*eps.val/R.val := by simp only [Rat.div_def]; grind only
  rw [he] at hb
  exact Small.congr (mul_valid (sub_valid F.property A.property) V.property)
    (centerErrorSample f a ha R hdom q).property
    (equiv_symm (centerErrorSample_value f a ha R hdom q hq)) hb

theorem inner_cauchy_center_estimate (f : DomainFunctions.Map) (a : Scalar) (ha : f.domain a) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) (eps : QPos)
    (hclose : ∀ z hz, Small (sub (f.eval (Centered.translate a z) (hdom z hz)).val (f.eval a ha).val) eps.val)
    (M : Nat) (hM : 0<M) :
    Small (sub (cauchyInnerPrefix f a R hdom M).val
      (mul (f.eval a ha).val (reciprocalInnerPrefix R M).val)) (64*eps.val) := by
  have hb := innerBoundary_inverse_error_bound (centerErrorSample f a ha R hdom) R M hM eps
    (centerErrorSample_bound f a ha R hdom eps hclose)
  exact Small.congr (innerBoundary (centerErrorSample f a ha R hdom) R M).property
    (gridScalarSub (cauchyInnerPrefix f a R hdom M) (scalarProduct (f.eval a ha) (reciprocalInnerPrefix R M))).property
    (centerErrorBoundary_identity f a ha R hdom M) hb

theorem reciprocalInnerPrefix_bound (R : QPos) (M : Nat) (hM : 0<M) :
    Small (reciprocalInnerPrefix R M).val 32 := by
  have hE : 0≤2/R.val := by
    rw [Rat.div_def]; exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr R.property))
  have hb := innerBoundary_bound (reciprocalFrameSample R) R M hM (2/R.val) hE (by
    intro q hq
    exact Small.congr (RepresentedReciprocal.inverse _ (frameDomain_nonzero R _ hq)).property
      (reciprocalFrameSample R q).property (equiv_symm (reciprocalFrameSample_value R q hq))
      (frame_rational_inverse_bound R q hq _))
  have hr := Rat.mul_inv_cancel R.val (Rat.ne_of_gt R.property)
  have hm := Rat.mul_inv_cancel (M:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  have he : 16*(M:Rat)*(2/R.val)*(R.val/(M:Rat))=32 := by simp only [Rat.div_def]; grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
