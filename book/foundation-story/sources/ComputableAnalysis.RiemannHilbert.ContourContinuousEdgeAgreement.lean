import ComputableAnalysis.RiemannHilbert.ContourContinuousEdges

/-! The continuous interval quadratures agree exactly with the existing
actual rectangle edge sampler, including vertical complex velocity. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

theorem intervalGridTag_horizontal_point (I : QInterval) (y : Rat) (M j : Nat) :
    rectangleGridHorizontalPoint (horizontalIntervalRectangle I y) M j 0=⟨intervalGridTag I M j,y⟩ := by
  simp only [rectangleGridHorizontalPoint,horizontalIntervalRectangle,intervalGridTag,
    intervalGridStep,rectangleGridStepX,rectangleGridStepY]
  simp [Rat.zero_mul,Rat.add_zero]

theorem intervalGridTag_vertical_point (I : QInterval) (x : Rat) (M j : Nat) :
    rectangleGridVerticalPoint (verticalIntervalRectangle I x) M 0 j=⟨x,intervalGridTag I M j⟩ := by
  simp only [rectangleGridVerticalPoint,verticalIntervalRectangle,intervalGridTag,
    intervalGridStep,rectangleGridStepX,rectangleGridStepY]
  simp [Rat.zero_mul,Rat.add_zero]

theorem gridValueSum_product_left (n : Nat) (a : ScalarAlgebra.Value) (f : Nat → ScalarAlgebra.Value) :
    gridValueSum n (fun j => a*f j)=a*gridValueSum n f := by
  induction n with
  | zero => simp only [gridValueSum]; grind only
  | succ n ih => simp only [gridValueSum,ih]; grind only

theorem gridScalarSum_product_left (n : Nat) (a : Scalar) (f : Nat → Scalar) :
    gridScalarSum n (fun j => scalarProduct a (f j)) ≈ scalarProduct a (gridScalarSum n f) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum n (fun j => scalarProduct a (f j))).property)
    (hright := (scalarProduct a (gridScalarSum n f)).property)
  change gridScalarValue (gridScalarSum n (fun j => scalarProduct a (f j)))=
    gridScalarValue a*gridScalarValue (gridScalarSum n f)
  simp only [gridScalarSum_value]
  change gridValueSum n (fun j => gridScalarValue a*gridScalarValue (f j))=
    gridScalarValue a*gridValueSum n (fun j => gridScalarValue (f j))
  exact gridValueSum_product_left n _ _

theorem horizontalInterval_weight (z : Scalar) (r : Rat) :
    scalarProduct z (rationalRectangleScalar ⟨r,0⟩) ≈ scale r z := by
  have h := rationalWeightedSample_scale z QComplex.one r
  simp only [QComplex.scaleRat,QComplex.one,Rat.mul_one,Rat.mul_zero] at h
  exact equiv_trans (scalarProduct z (rationalRectangleScalar ⟨r,0⟩)).property
    (scaleRat_valid (mul_valid z.property (ofQComplex_valid _))) (scale r z).property h
    (scaleRat_equiv (mul_one_equiv z.val z.property))

theorem verticalInterval_weight (z : Scalar) (r : Rat) :
    scalarProduct z (rationalRectangleScalar ⟨0,r⟩) ≈
      scalarProduct (rationalRectangleScalar ⟨0,1⟩) (scale r z) := by
  let v := rationalRectangleScalar (⟨0,1⟩ : QComplex)
  have h := rationalWeightedSample_scale z (⟨0,1⟩ : QComplex) r
  simp only [QComplex.scaleRat,Rat.mul_zero,Rat.mul_one] at h
  apply equiv_trans (scalarProduct z (rationalRectangleScalar ⟨0,r⟩)).property
    (scaleRat_valid (scalarProduct z v).property) (scalarProduct v (scale r z)).property h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid (scalarProduct z v).property)
    (hright := (scalarProduct v (scale r z)).property)
  let Z := gridScalarValue z
  let V := gridScalarValue v
  change ComplexRawQuotient.scaleRat r (Z*V)=V*ComplexRawQuotient.scaleRat r Z
  rw [ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.mul_comm Z V]

theorem horizontalContinuousPrefix_actualEdge (f : DomainFunctions.Map) (I : QInterval) (y : Rat)
    (hdom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (n : Nat) :
    gridScalarSum (2^n) (fun j => rectangleGridHorizontal
      (continuousRectangleSample f (horizontalIntervalRectangle I y) hdom)
        (horizontalIntervalRectangle I y) (2^n) j 0) ≈ horizontalContinuousPrefix f I y hdom n := by
  apply gridScalarSum_congr (2^n)
  intro j
  unfold rectangleGridHorizontal
  rw [intervalGridTag_horizontal_point]
  exact horizontalInterval_weight _ _

theorem verticalContinuousPrefix_actualEdge (f : DomainFunctions.Map) (I : QInterval) (x : Rat)
    (hdom : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (n : Nat) :
    gridScalarSum (2^n) (fun j => rectangleGridVertical
      (continuousRectangleSample f (verticalIntervalRectangle I x) hdom)
        (verticalIntervalRectangle I x) (2^n) 0 j) ≈ verticalContinuousPrefix f I x hdom n := by
  have he : gridScalarSum (2^n) (fun j => rectangleGridVertical
      (continuousRectangleSample f (verticalIntervalRectangle I x) hdom)
        (verticalIntervalRectangle I x) (2^n) 0 j) ≈
      gridScalarSum (2^n) (fun j => scalarProduct (rationalRectangleScalar ⟨0,1⟩)
        (scale (intervalGridStep I (2^n)) (verticalIntervalSample f I x hdom (intervalGridTag I (2^n) j)))) := by
    apply gridScalarSum_congr (2^n)
    intro j
    unfold rectangleGridVertical
    rw [intervalGridTag_vertical_point]
    exact verticalInterval_weight _ _
  exact Setoid.trans he (gridScalarSum_product_left (2^n) _ _)

end ComputableAnalysis.RiemannHilbert.RectangularContour
