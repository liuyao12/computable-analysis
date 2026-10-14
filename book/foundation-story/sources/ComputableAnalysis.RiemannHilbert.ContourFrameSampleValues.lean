import ComputableAnalysis.RiemannHilbert.ContourInnerBounds

/-! Exact values of the actual shared Cauchy and reciprocal samplers. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem frameSample_on_frame (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q)) :
    frameSample f R hdom q ≈ f.eval (rationalRectangleScalar q) (hdom _ hq) := by
  obtain ⟨j,k,hi,hrect⟩ := hq
  have hr : rationalRectangleContains (squareFrameTile R j k) q :=
    ⟨hrect.1 0 0,hrect.2.1 0 0,hrect.2.2.1 0 0,hrect.2.2.2 0 0⟩
  exact frameSample_agreement f R hdom j k hi q hr _

def reciprocalFrameSample (R : QPos) : QComplex → Scalar :=
  frameSample ReciprocalHolomorphic.function R (frameDomain_nonzero R)

theorem reciprocalFrameSample_value (R : QPos) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q)) :
    reciprocalFrameSample R q ≈
      RepresentedReciprocal.inverse (rationalRectangleScalar q) (frameDomain_nonzero R _ hq) :=
  frameSample_on_frame _ R (frameDomain_nonzero R) q hq

def cauchyFrameSample (f : DomainFunctions.Map) (a : Scalar) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) : QComplex → Scalar :=
  frameSample (cauchyKernel f a) R (cauchyKernel_frame_domain f a R hdom)

theorem cauchyFrameSample_value (f : DomainFunctions.Map) (a : Scalar) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q)) :
    cauchyFrameSample f a R hdom q ≈
      scalarProduct (f.eval (Centered.translate a (rationalRectangleScalar q)) (hdom _ hq))
        (RepresentedReciprocal.inverse (rationalRectangleScalar q) (frameDomain_nonzero R _ hq)) := by
  exact Setoid.trans (frameSample_on_frame _ R (cauchyKernel_frame_domain f a R hdom) q hq)
    (cauchyKernel_value f a _ (cauchyKernel_frame_domain f a R hdom _ hq) (hdom _ hq))

def centerErrorSample (f : DomainFunctions.Map) (a : Scalar) (ha : f.domain a) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) : QComplex → Scalar :=
  sampleLinear oneScalar (scalarNeg (f.eval a ha)) (cauchyFrameSample f a R hdom) (reciprocalFrameSample R)

theorem centerErrorSample_value (f : DomainFunctions.Map) (a : Scalar) (ha : f.domain a) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate a z)) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q)) :
    centerErrorSample f a ha R hdom q ≈
      scalarProduct (gridScalarSub (f.eval (Centered.translate a (rationalRectangleScalar q)) (hdom _ hq))
        (f.eval a ha)) (RepresentedReciprocal.inverse (rationalRectangleScalar q) (frameDomain_nonzero R _ hq)) := by
  let K := cauchyFrameSample f a R hdom q
  let P := reciprocalFrameSample R q
  let F := f.eval (Centered.translate a (rationalRectangleScalar q)) (hdom _ hq)
  let A := f.eval a ha
  let V := RepresentedReciprocal.inverse (rationalRectangleScalar q) (frameDomain_nonzero R _ hq)
  have hk := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := K.property)
    (hright := (scalarProduct F V).property) (cauchyFrameSample_value f a R hdom q hq)
  have hp := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := P.property)
    (hright := V.property) (reciprocalFrameSample_value R q hq)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (centerErrorSample f a ha R hdom q).property)
    (hright := (scalarProduct (gridScalarSub F A) V).property)
  change gridScalarValue K=gridScalarValue F*gridScalarValue V at hk
  change gridScalarValue P=gridScalarValue V at hp
  change 1*gridScalarValue K+(-gridScalarValue A)*gridScalarValue P=
    (gridScalarValue F-gridScalarValue A)*gridScalarValue V
  grind only

end ComputableAnalysis.RiemannHilbert.RectangularContour
