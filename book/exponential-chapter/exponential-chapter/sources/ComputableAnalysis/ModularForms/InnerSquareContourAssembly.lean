import ComputableAnalysis.ModularForms.InnerSquareReversedEdges

/-! The assembled inner frame contour agrees with the original square sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

def originalHalfEdgeValue (c : Scalar) (S : Rat) (M : Nat) (e : HalfEdge) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (pairedSquareHalfEdgeSum c e S M) (pairedSquareHalfEdgeSum_valid c e S M)

def originalEdgeListValue (c : Scalar) (S : Rat) (M : Nat) : List HalfEdge → ScalarAlgebra.Value
  | [] => 0
  | e::es => originalHalfEdgeValue c S M e+originalEdgeListValue c S M es

theorem originalEdgeListValue_agreement (c : Scalar) (S : Rat) (M : Nat) (es : List HalfEdge) :
    ComplexRawQuotient.ofRaw (pairedSquareEdgeListSum c S M es)
      (pairedSquareEdgeListSum_valid c S M es)=originalEdgeListValue c S M es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change ComplexRawQuotient.ofRaw (add (pairedSquareHalfEdgeSum c e S M)
      (pairedSquareEdgeListSum c S M es)) _=_
    rw [ComplexRawQuotient.ofRaw_add _ _ (pairedSquareHalfEdgeSum_valid c e S M) (pairedSquareEdgeListSum_valid c S M es)]
    rw [ih]
    rfl

def assembledInnerSquareContour (c : Scalar) (R : QPos) (M : Nat) : Scalar :=
  frameScalarRectBoundary (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M)
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M) 1 1 2 2

theorem assembledInnerSquareContour_agreement (c : Scalar) (R : QPos) (M : Nat) (hM : 0<M) :
    (assembledInnerSquareContour c R M).val.Equiv (pairedSquareContourSum c R.val M) := by
  let H := squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M
  let V := squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M
  have he (u : Bool) : gridScalarValue (V 3 (if u then 2 else 1))=
      originalHalfEdgeValue c R.val M ⟨.east,u⟩ :=
    ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (V 3 (if u then 2 else 1)).property)
      (hright := pairedSquareHalfEdgeSum_valid c ⟨.east,u⟩ R.val M)
      (squareFrame_inner_right_tile_original_agreement c R M hM u)
  have hs (u : Bool) : gridScalarValue (H (if u then 2 else 1) 1)=
      originalHalfEdgeValue c R.val M ⟨.south,u⟩ :=
    ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (H (if u then 2 else 1) 1).property)
      (hright := pairedSquareHalfEdgeSum_valid c ⟨.south,u⟩ R.val M)
      (squareFrame_inner_bottom_tile_original_agreement c R M hM u)
  have hn (u : Bool) : gridScalarValue (H (if u then 1 else 2) 3)=
      -originalHalfEdgeValue c R.val M ⟨.north,u⟩ := by
    have ha := squareFrame_inner_top_tile_sum c R M hM u
    have hb := negativeCartesianHalfEdgeSum_agreement c .north R.val M hM u
    have ht := equiv_trans (H (if u then 1 else 2) 3).property
      (negativeCartesianHalfEdgeSum c .north R.val M u).property
      (neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.north,u⟩ R.val M)) ha hb
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (H (if u then 1 else 2) 3).property)
      (hright := neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.north,u⟩ R.val M)) ht
    rw [ComplexRawQuotient.ofRaw_neg _ (pairedSquareHalfEdgeSum_valid c ⟨.north,u⟩ R.val M)] at hv
    exact hv
  have hw (u : Bool) : gridScalarValue (V 1 (if u then 1 else 2))=
      -originalHalfEdgeValue c R.val M ⟨.west,u⟩ := by
    have ha := squareFrame_inner_left_tile_sum c R M hM u
    have hb := negativeCartesianHalfEdgeSum_agreement c .west R.val M hM u
    have ht := equiv_trans (V 1 (if u then 1 else 2)).property
      (negativeCartesianHalfEdgeSum c .west R.val M u).property
      (neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.west,u⟩ R.val M)) ha hb
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (V 1 (if u then 1 else 2)).property)
      (hright := neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.west,u⟩ R.val M)) ht
    rw [ComplexRawQuotient.ofRaw_neg _ (pairedSquareHalfEdgeSum_valid c ⟨.west,u⟩ R.val M)] at hv
    exact hv
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (assembledInnerSquareContour c R M).property)
    (hright := pairedSquareContourSum_valid c R.val M)
  change gridScalarValue (frameScalarRectBoundary H V 1 1 2 2)=
    ComplexRawQuotient.ofRaw (pairedSquareEdgeListSum c R.val M PDE.CauchyContour.square) _
  rw [frameScalarRectBoundary_value,originalEdgeListValue_agreement]
  have he0 := he false; have he1 := he true
  have hs0 := hs false; have hs1 := hs true
  have hn0 := hn false; have hn1 := hn true
  have hw0 := hw false; have hw1 := hw true
  simp only [Bool.false_eq_true,↓reduceIte] at he0 he1 hs0 hs1 hn0 hn1 hw0 hw1
  simp only [frameValueRectBoundary,gridValueBoundary,gridValueSum,
    PDE.CauchyContour.square,originalEdgeListValue]
  rw [he0,he1,hs0,hs1,hn0,hn1,hw0,hw1]
  grind only

end ComputableAnalysis.ModularForms
