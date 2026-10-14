import ComputableAnalysis.ModularForms.OuterSquareReversedTiles

/-! The assembled outer contour agrees with the original doubled square sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

def assembledOuterSquareContour (c : Scalar) (R : QPos) (M : Nat) : Scalar :=
  frameScalarRectBoundary (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M)
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M) 0 0 4 4

theorem assembledOuterSquareContour_agreement (c : Scalar) (R : QPos) (M : Nat) (hM : 0<M) :
    (assembledOuterSquareContour c R M).val.Equiv (pairedSquareContourSum c (2*R.val) (2*M)) := by
  let H := squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M
  let V := squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M
  have he (u : Bool) : gridScalarValue (V 4 (if u then 2 else 0))+gridScalarValue (V 4 ((if u then 2 else 0)+1))=originalHalfEdgeValue c (2*R.val) (2*M) ⟨.east,u⟩ := by
    have ht := squareFrame_outer_right_half_sum c R M hM u
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (scalarSum (V 4 (if u then 2 else 0)) (V 4 ((if u then 2 else 0)+1))).property)
      (hright := pairedSquareHalfEdgeSum_valid c ⟨.east,u⟩ (2*R.val) (2*M)) ht
    change gridScalarValue (scalarSum (V 4 (if u then 2 else 0)) (V 4 ((if u then 2 else 0)+1)))=_ at hv
    rw [gridScalarValue_add] at hv
    exact hv
  have hs (u : Bool) : gridScalarValue (H (if u then 2 else 0) 0)+gridScalarValue (H ((if u then 2 else 0)+1) 0)=originalHalfEdgeValue c (2*R.val) (2*M) ⟨.south,u⟩ := by
    have ht := squareFrame_outer_bottom_half_sum c R M hM u
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (scalarSum (H (if u then 2 else 0) 0) (H ((if u then 2 else 0)+1) 0)).property)
      (hright := pairedSquareHalfEdgeSum_valid c ⟨.south,u⟩ (2*R.val) (2*M)) ht
    change gridScalarValue (scalarSum (H (if u then 2 else 0) 0) (H ((if u then 2 else 0)+1) 0))=_ at hv
    rw [gridScalarValue_add] at hv
    exact hv
  have hn (u : Bool) : gridScalarValue (H ((if u then 0 else 2)+1) 4)+gridScalarValue (H (if u then 0 else 2) 4)=-originalHalfEdgeValue c (2*R.val) (2*M) ⟨.north,u⟩ := by
    have ht := squareFrame_outer_top_half_sum c R M hM u
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (scalarSum (H ((if u then 0 else 2)+1) 4) (H (if u then 0 else 2) 4)).property)
      (hright := neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.north,u⟩ (2*R.val) (2*M))) ht
    rw [ComplexRawQuotient.ofRaw_neg _ (pairedSquareHalfEdgeSum_valid c ⟨.north,u⟩ (2*R.val) (2*M))] at hv
    change gridScalarValue (scalarSum (H ((if u then 0 else 2)+1) 4) (H (if u then 0 else 2) 4))=_ at hv
    rw [gridScalarValue_add] at hv
    exact hv
  have hw (u : Bool) : gridScalarValue (V 0 ((if u then 0 else 2)+1))+gridScalarValue (V 0 (if u then 0 else 2))=-originalHalfEdgeValue c (2*R.val) (2*M) ⟨.west,u⟩ := by
    have ht := squareFrame_outer_left_half_sum c R M hM u
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (scalarSum (V 0 ((if u then 0 else 2)+1)) (V 0 (if u then 0 else 2))).property)
      (hright := neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.west,u⟩ (2*R.val) (2*M))) ht
    rw [ComplexRawQuotient.ofRaw_neg _ (pairedSquareHalfEdgeSum_valid c ⟨.west,u⟩ (2*R.val) (2*M))] at hv
    change gridScalarValue (scalarSum (V 0 ((if u then 0 else 2)+1)) (V 0 (if u then 0 else 2)))=_ at hv
    rw [gridScalarValue_add] at hv
    exact hv
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (assembledOuterSquareContour c R M).property)
    (hright := pairedSquareContourSum_valid c (2*R.val) (2*M))
  change gridScalarValue (frameScalarRectBoundary H V 0 0 4 4)=
    ComplexRawQuotient.ofRaw (pairedSquareEdgeListSum c (2*R.val) (2*M) PDE.CauchyContour.square) _
  rw [frameScalarRectBoundary_value,originalEdgeListValue_agreement]
  have he0 := he false; have he1 := he true
  have hs0 := hs false; have hs1 := hs true
  have hn0 := hn false; have hn1 := hn true
  have hw0 := hw false; have hw1 := hw true
  simp only [Bool.false_eq_true,↓reduceIte] at he0 he1 hs0 hs1 hn0 hn1 hw0 hw1
  simp only [frameValueRectBoundary,gridValueBoundary,gridValueSum,
    PDE.CauchyContour.square,originalEdgeListValue]
  grind only

theorem pairedSquareContourSum_doubled_radius_difference_converges_zero
    (c : Scalar) (R eps : QPos) :
    ∃ N, ∀ n, N≤n →
      Small (sub (pairedSquareContourSum c (2*R.val) (2*(2^n)))
        (pairedSquareContourSum c R.val (2^n))) eps.val := by
  obtain ⟨N,hN⟩ := puncturedKernel_squareFrameContourDifference_converges_zero c R eps
  refine ⟨N, ?_⟩
  intro n hn
  have hp : 0<2^n := Nat.pow_pos (by decide)
  have he := FunctionTheory.sub_congr
    (assembledOuterSquareContour_agreement c R (2^n) hp)
    (assembledInnerSquareContour_agreement c R (2^n) hp)
  exact Small.congr (puncturedKernel_squareFrameContourDifference c R n).property
    (sub_valid (pairedSquareContourSum_valid c (2*R.val) (2*(2^n)))
      (pairedSquareContourSum_valid c R.val (2^n))) he (hN n hn)

end ComputableAnalysis.ModularForms

