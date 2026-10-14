import ComputableAnalysis.ModularForms.RepresentedAffinePoleDensity

/-! Exact whole-square affine residue for arbitrary represented coefficients. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem rationalPole_add_values (p q : QComplex) :
    gridScalarValue (rationalRectangleScalar (QComplex.add p q))=
      gridScalarValue (rationalRectangleScalar p)+gridScalarValue (rationalRectangleScalar q) := by
  have he : (add (ofQComplex p) (ofQComplex q)).Equiv (ofQComplex (QComplex.add p q)) := by
    intro k
    apply (compareAt_overlap_iff _ _ k k).2
    apply QBox.overlaps_of_common_point (point := QComplex.add p q)
    · exact QBox.add_contains (QComplex.le_refl _) (QComplex.le_refl _)
        (QComplex.le_refl _) (QComplex.le_refl _)
    · exact ⟨QComplex.le_refl _,QComplex.le_refl _⟩
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid (ofQComplex_valid p) (ofQComplex_valid q))
    (hright := ofQComplex_valid (QComplex.add p q)) he
  rw [ComplexRawQuotient.ofRaw_add _ _ (ofQComplex_valid p) (ofQComplex_valid q)] at hv
  exact hv.symm

theorem poleCoefficientEdgeList_fold (A : Scalar) (kernel : HalfEdge → QComplex) (es : List HalfEdge) :
    (poleCoefficientEdgeList A kernel es).val.Equiv
      (scalarProduct A (rationalRectangleScalar ((es.map kernel).foldr QComplex.add QComplex.zero))).val := by
  induction es with
  | nil =>
    exact equiv_symm (mul_zero_equiv A.val A.property)
  | cons e es ih =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (poleCoefficientEdgeList A kernel (e::es)).property)
      (hright := (scalarProduct A (rationalRectangleScalar (((e::es).map kernel).foldr QComplex.add QComplex.zero))).property)
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (poleCoefficientEdgeList A kernel es).property)
      (hright := (scalarProduct A (rationalRectangleScalar ((es.map kernel).foldr QComplex.add QComplex.zero))).property) ih
    change gridScalarValue (poleCoefficientEdgeList A kernel es)=
      gridScalarValue (scalarProduct A (rationalRectangleScalar ((es.map kernel).foldr QComplex.add QComplex.zero))) at hv
    change gridScalarValue (scalarSum (scalarProduct A (rationalRectangleScalar (kernel e)))
      (poleCoefficientEdgeList A kernel es))=
      gridScalarValue (scalarProduct A (rationalRectangleScalar (QComplex.add (kernel e)
        ((es.map kernel).foldr QComplex.add QComplex.zero))))
    rw [gridScalarValue_add,hv]
    have ha := rationalPole_add_values (kernel e) ((es.map kernel).foldr QComplex.add QComplex.zero)
    let X := gridScalarValue A
    let P := gridScalarValue (rationalRectangleScalar (kernel e))
    let Q := gridScalarValue (rationalRectangleScalar ((es.map kernel).foldr QComplex.add QComplex.zero))
    let S := gridScalarValue (rationalRectangleScalar (QComplex.add (kernel e)
      ((es.map kernel).foldr QComplex.add QComplex.zero)))
    change S=P+Q at ha
    change X*P+X*Q=X*S
    rw [ha]
    grind only

theorem representedSquare_affine_residue_density (A d : Scalar) (R u : Rat) (hR : 0<R) :
    (affinePoleEdgeList A d R u PDE.CauchyContour.square).val.Equiv
      (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩)).val := by
  have h0 := poleCoefficientEdgeList_fold A (fun e => squaredPolePullback e R u) PDE.CauchyContour.square
  have h1 := poleCoefficientEdgeList_fold d (fun e => linearPolePullback e R u) PDE.CauchyContour.square
  change (poleCoefficientEdgeList A (fun e => squaredPolePullback e R u) PDE.CauchyContour.square).val.Equiv
    (scalarProduct A (rationalRectangleScalar (squaredPoleDensity R u))).val at h0
  rw [squaredPoleDensity_zero R u] at h0
  rw [linearPole_square_density R u hR] at h1
  have ha := affinePoleEdgeList_decomposition A d R u PDE.CauchyContour.square
  have hb := add_equiv h0 h1
  have hc : (scalarSum (scalarProduct A (rationalRectangleScalar QComplex.zero))
      (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩))).val.Equiv
      (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩)).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (scalarSum (scalarProduct A (rationalRectangleScalar QComplex.zero))
        (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩))).property)
      (hright := (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩)).property)
    let X := gridScalarValue A
    let Y := gridScalarValue (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩))
    change X*0+Y=Y
    grind only
  exact equiv_trans (affinePoleEdgeList A d R u PDE.CauchyContour.square).property
    (scalarSum (poleCoefficientEdgeList A (fun e => squaredPolePullback e R u) PDE.CauchyContour.square)
      (poleCoefficientEdgeList d (fun e => linearPolePullback e R u) PDE.CauchyContour.square)).property
    (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩)).property ha
    (equiv_trans
      (scalarSum (poleCoefficientEdgeList A (fun e => squaredPolePullback e R u) PDE.CauchyContour.square)
        (poleCoefficientEdgeList d (fun e => linearPolePullback e R u) PDE.CauchyContour.square)).property
      (scalarSum (scalarProduct A (rationalRectangleScalar QComplex.zero))
        (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩))).property
      (scalarProduct d (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩)).property hb hc)

end ComputableAnalysis.ModularForms
