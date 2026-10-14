import ComputableAnalysis.RiemannHilbert.ContourBoundaryFinite

namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

theorem rectangleBoundaryDomains_rational (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : RectangleBoundaryDomains f J) (q : QComplex) (hq : rationalRectangleBoundaryContains J q) :
    f.domain (rationalRectangleScalar q) := by
  rcases hq with hq|hq|hq|hq
  · exact hd.bottom _ (rationalRectangle_represented_mem _ q hq)
  · exact hd.top _ (rationalRectangle_represented_mem _ q hq)
  · exact hd.left _ (rationalRectangle_represented_mem _ q hq)
  · exact hd.right _ (rationalRectangle_represented_mem _ q hq)

theorem rectangleGridBoundary_scale (f : QComplex → Scalar) (J : QInterval × QInterval) (M : Nat) (r : Rat) :
    rectangleGridBoundary (fun q => scale r (f q)) J M≈scale r (rectangleGridBoundary f J M) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (rectangleGridBoundary (fun q => scale r (f q)) J M).property)
    (hright := (scale r (rectangleGridBoundary f J M)).property)
  have hH (j k : Nat) : gridScalarValue (rectangleGridHorizontal (fun q => scale r (f q)) J M j k)=
      ComplexRawQuotient.scaleRat r (gridScalarValue (rectangleGridHorizontal f J M j k)) := by
    change ComplexRawQuotient.scaleRat r (gridScalarValue (f _))*gridScalarValue (rationalRectangleScalar _)=
      ComplexRawQuotient.scaleRat r (gridScalarValue (f _)*gridScalarValue (rationalRectangleScalar _))
    exact (ComplexRawQuotient.scaleRat_mul _ _ _).symm
  have hV (j k : Nat) : gridScalarValue (rectangleGridVertical (fun q => scale r (f q)) J M j k)=
      ComplexRawQuotient.scaleRat r (gridScalarValue (rectangleGridVertical f J M j k)) := by
    change ComplexRawQuotient.scaleRat r (gridScalarValue (f _))*gridScalarValue (rationalRectangleScalar _)=
      ComplexRawQuotient.scaleRat r (gridScalarValue (f _)*gridScalarValue (rationalRectangleScalar _))
    exact (ComplexRawQuotient.scaleRat_mul _ _ _).symm
  have hsub (u v : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat r u-ComplexRawQuotient.scaleRat r v=
      ComplexRawQuotient.scaleRat r (u-v) := by
    change ComplexRawQuotient.scaleRat r u+ -(ComplexRawQuotient.scaleRat r v)=ComplexRawQuotient.scaleRat r (u+ -v)
    rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_eq_scaleRat_neg_one v,
      ComplexRawQuotient.scaleRat_scaleRat,ComplexRawQuotient.neg_scaleRat]
    rw [show r*(-1)= -r by grind only]
  change gridScalarValue (rectangleGridBoundary (fun q => scale r (f q)) J M)=
    ComplexRawQuotient.scaleRat r (gridScalarValue (rectangleGridBoundary f J M))
  simp only [rectangleGridBoundary,gridScalarBoundary,gridScalarValue_add,gridScalarSum_value,
    gridScalarValue_sub,hH,hV,hsub,gridValueSum_scale,
    ComplexRawQuotient.scaleRat_add]

theorem rectangleGridBoundary_scaled_difference (f g : QComplex → Scalar) (J : QInterval × QInterval)
    (M : Nat) (r : Rat) :
    rectangleGridBoundary (fun q => scale r (gridScalarSub (f q) (g q))) J M≈
      scale r (gridScalarSub (rectangleGridBoundary f J M) (rectangleGridBoundary g J M)) :=
  Setoid.trans (rectangleGridBoundary_scale _ J M r)
    (scaleRat_equiv (rectangleGridBoundary_difference f g J M))

end ComputableAnalysis.RiemannHilbert.RectangularContour
