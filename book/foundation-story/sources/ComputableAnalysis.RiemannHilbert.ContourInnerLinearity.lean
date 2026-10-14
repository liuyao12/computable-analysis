import ComputableAnalysis.RiemannHilbert.ContourInnerGeometry

/-! Finite inner contours are linear in their actual represented samples.
All coefficients may be irrational represented values. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def sampleLinear (a b : Scalar) (f g : QComplex → Scalar) (q : QComplex) : Scalar :=
  scalarSum (scalarProduct a (f q)) (scalarProduct b (g q))

theorem gridValueSum_linear (n : Nat) (a b : ScalarAlgebra.Value)
    (f g : Nat → ScalarAlgebra.Value) :
    gridValueSum n (fun j => a*f j+b*g j)=a*gridValueSum n f+b*gridValueSum n g := by
  induction n with
  | zero => simp only [gridValueSum]; grind only
  | succ n ih => simp only [gridValueSum,ih]; grind only

theorem horizontalSample_linear (a b : Scalar) (f g : QComplex → Scalar)
    (J : QInterval × QInterval) (M j k : Nat) :
    gridScalarValue (rectangleGridHorizontal (sampleLinear a b f g) J M j k)=
      gridScalarValue a*gridScalarValue (rectangleGridHorizontal f J M j k)+
        gridScalarValue b*gridScalarValue (rectangleGridHorizontal g J M j k) := by
  let A := gridScalarValue a
  let B := gridScalarValue b
  let F := gridScalarValue (f (rectangleGridHorizontalPoint J M j k))
  let G := gridScalarValue (g (rectangleGridHorizontalPoint J M j k))
  let V := gridScalarValue (rationalRectangleScalar ⟨rectangleGridStepX J M,0⟩)
  change (A*F+B*G)*V=A*(F*V)+B*(G*V)
  grind only

theorem verticalSample_linear (a b : Scalar) (f g : QComplex → Scalar)
    (J : QInterval × QInterval) (M j k : Nat) :
    gridScalarValue (rectangleGridVertical (sampleLinear a b f g) J M j k)=
      gridScalarValue a*gridScalarValue (rectangleGridVertical f J M j k)+
        gridScalarValue b*gridScalarValue (rectangleGridVertical g J M j k) := by
  let A := gridScalarValue a
  let B := gridScalarValue b
  let F := gridScalarValue (f (rectangleGridVerticalPoint J M j k))
  let G := gridScalarValue (g (rectangleGridVerticalPoint J M j k))
  let V := gridScalarValue (rationalRectangleScalar ⟨0,rectangleGridStepY J M⟩)
  change (A*F+B*G)*V=A*(F*V)+B*(G*V)
  grind only

theorem horizontalEdge_linear (a b : Scalar) (f g : QComplex → Scalar)
    (R : QPos) (M j k : Nat) :
    gridScalarValue (squareFrameHorizontalEdge (sampleLinear a b f g) R M j k)=
      gridScalarValue a*gridScalarValue (squareFrameHorizontalEdge f R M j k)+
        gridScalarValue b*gridScalarValue (squareFrameHorizontalEdge g R M j k) := by
  simp only [squareFrameHorizontalEdge,gridScalarSum_value,horizontalSample_linear]
  exact gridValueSum_linear _ _ _ _ _

theorem verticalEdge_linear (a b : Scalar) (f g : QComplex → Scalar)
    (R : QPos) (M j k : Nat) :
    gridScalarValue (squareFrameVerticalEdge (sampleLinear a b f g) R M j k)=
      gridScalarValue a*gridScalarValue (squareFrameVerticalEdge f R M j k)+
        gridScalarValue b*gridScalarValue (squareFrameVerticalEdge g R M j k) := by
  simp only [squareFrameVerticalEdge,gridScalarSum_value,verticalSample_linear]
  exact gridValueSum_linear _ _ _ _ _

theorem innerBoundary_linear (a b : Scalar) (f g : QComplex → Scalar) (R : QPos) (M : Nat) :
    innerBoundary (sampleLinear a b f g) R M ≈
      scalarSum (scalarProduct a (innerBoundary f R M)) (scalarProduct b (innerBoundary g R M)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (innerBoundary (sampleLinear a b f g) R M).property)
    (hright := (scalarSum (scalarProduct a (innerBoundary f R M))
      (scalarProduct b (innerBoundary g R M))).property)
  change gridScalarValue (innerBoundary (sampleLinear a b f g) R M)=
    gridScalarValue a*gridScalarValue (innerBoundary f R M)+
      gridScalarValue b*gridScalarValue (innerBoundary g R M)
  simp only [innerBoundary,frameScalarRectBoundary_value,frameValueRectBoundary,gridValueBoundary,
    gridValueSum,horizontalEdge_linear,verticalEdge_linear]
  grind only

end ComputableAnalysis.RiemannHilbert.RectangularContour
