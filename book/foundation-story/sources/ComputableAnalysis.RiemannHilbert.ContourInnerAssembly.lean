import ComputableAnalysis.RiemannHilbert.ContourInnerReverseSides

/-! Eight actual inner half edges assembled in counterclockwise order. Generic finite proofs adapted from the corresponding
`ModularForms` files; those original files are preserved. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

def commonSquareEdgeListValue (f : QComplex → Scalar) (R : QPos) (M : Nat) :
    List HalfEdge → ScalarAlgebra.Value
  | [] => 0
  | e::es =>
    let v := gridScalarValue (commonSquareKernelAverage f e R M)
    (if e.upper then v else -v)+commonSquareEdgeListValue f R M es

theorem gridScalarValue_scalarNeg (a : Scalar) : gridScalarValue (scalarNeg a)= -gridScalarValue a :=
  ComplexRawQuotient.ofRaw_neg _ a.property

theorem commonSquareEdgeListValue_agreement (f : QComplex → Scalar)
    (R : QPos) (M : Nat) (es : List HalfEdge) :
    gridScalarValue (commonSquareKernelEdgeList f R M es)=commonSquareEdgeListValue f R M es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases h : e.upper
    · change gridScalarValue (scalarSum
        (if e.upper then commonSquareKernelAverage f e R M else scalarNeg (commonSquareKernelAverage f e R M))
        (commonSquareKernelEdgeList f R M es)) = _
      rw [h]
      simp only [Bool.false_eq_true,↓reduceIte,gridScalarValue_add,gridScalarValue_scalarNeg,
        commonSquareEdgeListValue,h,ih]
    · change gridScalarValue (scalarSum
        (if e.upper then commonSquareKernelAverage f e R M else scalarNeg (commonSquareKernelAverage f e R M))
        (commonSquareKernelEdgeList f R M es)) = _
      rw [h]
      simp only [↓reduceIte,gridScalarValue_add,commonSquareEdgeListValue,h,ih]

/-- All half-edge comparisons assembled, for an arbitrary supplied sampler. -/
theorem commonInnerSquareContour_agreement (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (frameScalarRectBoundary (squareFrameHorizontalEdge f R M)
      (squareFrameVerticalEdge f R M) 1 1 2 2).val.Equiv
      (commonSquareKernelEdgeList f R M PDE.CauchyContour.square).val := by
  let H := squareFrameHorizontalEdge f R M
  let V := squareFrameVerticalEdge f R M
  let A := fun e => commonSquareKernelAverage f e R M
  have value {x y : Scalar} (he : x.val.Equiv y.val) : gridScalarValue x=gridScalarValue y :=
    ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := x.property) (hright := y.property) he
  have negative {x y : Scalar} (he : x.val.Equiv (neg y.val)) :
      gridScalarValue x= -gridScalarValue y := by
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := x.property)
      (hright := neg_valid y.property) he
    rw [ComplexRawQuotient.ofRaw_neg _ y.property] at hv
    exact hv
  have he0 : gridScalarValue (V 3 1)= -gridScalarValue (A ⟨.east,false⟩) :=
    negative (common_inner_right_lower_average f R M hM)
  have he1 : gridScalarValue (V 3 2)=gridScalarValue (A ⟨.east,true⟩) :=
    value (common_inner_right_upper_average f R M hM)
  have hs0 : gridScalarValue (H 1 1)= -gridScalarValue (A ⟨.south,false⟩) :=
    negative (common_inner_bottom_lower_average f R M hM)
  have hs1 : gridScalarValue (H 2 1)=gridScalarValue (A ⟨.south,true⟩) :=
    value (common_inner_bottom_upper_average f R M hM)
  have hn0 : gridScalarValue (H 2 3)=gridScalarValue (A ⟨.north,false⟩) :=
    value (common_inner_top_lower_average f R M hM)
  have hn1 : gridScalarValue (H 1 3)= -gridScalarValue (A ⟨.north,true⟩) :=
    negative (common_inner_top_upper_average f R M hM)
  have hw0 : gridScalarValue (V 1 2)=gridScalarValue (A ⟨.west,false⟩) :=
    value (common_inner_left_lower_average f R M hM)
  have hw1 : gridScalarValue (V 1 1)= -gridScalarValue (A ⟨.west,true⟩) :=
    negative (common_inner_left_upper_average f R M hM)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (frameScalarRectBoundary H V 1 1 2 2).property)
    (hright := (commonSquareKernelEdgeList f R M PDE.CauchyContour.square).property)
  change gridScalarValue (frameScalarRectBoundary H V 1 1 2 2)=
    gridScalarValue (commonSquareKernelEdgeList f R M PDE.CauchyContour.square)
  rw [frameScalarRectBoundary_value,commonSquareEdgeListValue_agreement]
  simp only [frameValueRectBoundary,gridValueBoundary,gridValueSum,PDE.CauchyContour.square,commonSquareEdgeListValue,
    Bool.false_eq_true,↓reduceIte]
  rw [he0,he1,hs0,hs1,hn0,hn1,hw0,hw1]
  dsimp only [A]
  grind only

end ComputableAnalysis.RiemannHilbert.RectangularContour
