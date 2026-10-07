import ComputableAnalysis.ModularForms.DomainSegmentBisection

/-! Width-scaled endpoint errors from actual derivative-continuity neighborhoods,
with whole-segment domain evidence kept separate from the estimate. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem domainNeighborhood_segment_remainder_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (a p q : Scalar) (ha : f.domain a) (hp : f.domain p) (hq : f.domain q) (W eps : QPos)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (hpa : Small (Centered.offset a p).val (hf.continuousDerivative.delta a ha eps).val)
    (hqa : Small (Centered.offset a q).val (hf.continuousDerivative.delta a ha eps).val) :
    Small (remainder f p hp (hf.derivative a ha) q hq) (4*eps.val*W.val) := by
  apply domainSegment_remainder_bound f hf p q (hf.derivative a ha) hp hq W eps hdom hd
  intro t
  exact hf.continuousDerivative.estimate a ha eps (RepresentedAffineSegment.point p q t) (hdom t)
    (RepresentedAffineSegment.offset_bound a p q t _ hpa hqa)

theorem puncturedRiccati_rectangle_segment_linearization (c a : Scalar)
    (ha : NonzeroBoxSearch.Nonzero a) (J : QInterval × QInterval) (R : QPos)
    (hs : rectangleSeparated J R) (p q : QComplex)
    (hp : rationalRectangleContains J p) (hq : rationalRectangleContains J q)
    (W eps : QPos) (hd : Small (sub (ofQComplex q) (ofQComplex p)) W.val)
    (hpa : Small (Centered.offset a (rationalRectangleScalar p)).val
      ((pairedRiccatiCauchyIntegrandMap_holomorphic c).continuousDerivative.delta a ha eps).val)
    (hqa : Small (Centered.offset a (rationalRectangleScalar q)).val
      ((pairedRiccatiCauchyIntegrandMap_holomorphic c).continuousDerivative.delta a ha eps).val) :
    Small (remainder (pairedRiccatiCauchyIntegrandMap c)
      (rationalRectangleScalar p)
      (punctureSafeRectangle_kernel_domain c J R hs _ (rationalRectangle_represented_mem J p hp))
      ((pairedRiccatiCauchyIntegrandMap_holomorphic c).derivative a ha)
      (rationalRectangleScalar q)
      (punctureSafeRectangle_kernel_domain c J R hs _ (rationalRectangle_represented_mem J q hq)))
      (4*eps.val*W.val) :=
  domainNeighborhood_segment_remainder_bound (pairedRiccatiCauchyIntegrandMap c)
    (pairedRiccatiCauchyIntegrandMap_holomorphic c) a (rationalRectangleScalar p) (rationalRectangleScalar q)
    ha _ _ W eps (punctureSafeAffineSegment_kernel_domain c J R hs p q hp hq) hd hpa hqa

end ComputableAnalysis.ModularForms
