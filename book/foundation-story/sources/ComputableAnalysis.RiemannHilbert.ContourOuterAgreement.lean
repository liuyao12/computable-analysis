import ComputableAnalysis.RiemannHilbert.ContourRadiusConcatenation

/-! Whole-frame sampler agreement for the outer boundary and exact comparison
with the doubled-radius inner boundary. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def outerBoundary (sample : QComplex → Scalar) (R : QPos) (M : Nat) : Scalar :=
  frameScalarRectBoundary (squareFrameHorizontalEdge sample R M) (squareFrameVerticalEdge sample R M) 0 0 4 4

theorem outerHorizontalPoint_mem (R : QPos) (M j k u : Nat) (hM : 0<M)
    (hj : j<4) (hk : k=0 ∨ k=4) (hu : u<M) :
    frameDomain R (rationalRectangleScalar (rectangleGridHorizontalPoint (squareFrameTile R j k) M u 0)) := by
  rcases hk with hk|hk
  · subst k
    have ho := squareFrameTile_ordered R j 0
    exact ⟨j,0,by unfold squareFrameTileIndex; omega,
      rationalRectangle_represented_mem _ _
        (rectangleGridHorizontalPoint_mem _ M u 0 ho.1 ho.2 hM hu (Nat.zero_le M))⟩
  · subst k
    rw [←squareFrameTile_shared_horizontal_points R M j 3 u hM]
    have ho := squareFrameTile_ordered R j 3
    exact ⟨j,3,by unfold squareFrameTileIndex; omega,
      rationalRectangle_represented_mem _ _
        (rectangleGridHorizontalPoint_mem _ M u M ho.1 ho.2 hM hu (Nat.le_refl M))⟩

theorem outerVerticalPoint_mem (R : QPos) (M j k u : Nat) (hM : 0<M)
    (hj : j=0 ∨ j=4) (hk : k<4) (hu : u<M) :
    frameDomain R (rationalRectangleScalar (rectangleGridVerticalPoint (squareFrameTile R j k) M 0 u)) := by
  rcases hj with hj|hj
  · subst j
    have ho := squareFrameTile_ordered R 0 k
    exact ⟨0,k,by unfold squareFrameTileIndex; omega,
      rationalRectangle_represented_mem _ _
        (rectangleGridVerticalPoint_mem _ M 0 u ho.1 ho.2 hM (Nat.zero_le M) hu)⟩
  · subst j
    rw [←squareFrameTile_shared_vertical_points R M 3 k u hM]
    have ho := squareFrameTile_ordered R 3 k
    exact ⟨3,k,by unfold squareFrameTileIndex; omega,
      rationalRectangle_represented_mem _ _
        (rectangleGridVerticalPoint_mem _ M M u ho.1 ho.2 hM (Nat.le_refl M) hu)⟩

theorem outerBoundary_congr_on_frame (f g : QComplex → Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (he : ∀ q, frameDomain R (rationalRectangleScalar q) → f q ≈ g q) :
    outerBoundary f R M ≈ outerBoundary g R M := by
  have hh (j k : Nat) (hj : j<4) (hk : k=0 ∨ k=4) :
      (squareFrameHorizontalEdge f R M j k).val.Equiv (squareFrameHorizontalEdge g R M j k).val := by
    apply gridScalarSum_congr_bounded M
    intro u hu
    exact mul_equiv (f _).property (g _).property (ofQComplex_valid _) (ofQComplex_valid _)
      (he _ (outerHorizontalPoint_mem R M j k u hM hj hk hu)) (equiv_refl _ (ofQComplex_valid _))
  have hv (j k : Nat) (hj : j=0 ∨ j=4) (hk : k<4) :
      (squareFrameVerticalEdge f R M j k).val.Equiv (squareFrameVerticalEdge g R M j k).val := by
    apply gridScalarSum_congr_bounded M
    intro u hu
    exact mul_equiv (f _).property (g _).property (ofQComplex_valid _) (ofQComplex_valid _)
      (he _ (outerVerticalPoint_mem R M j k u hM hj hk hu)) (equiv_refl _ (ofQComplex_valid _))
  change (frameScalarRectBoundary _ _ 0 0 4 4).val.Equiv _
  unfold frameScalarRectBoundary
  apply add_equiv
  · apply gridScalarSum_congr_bounded 4
    intro u hu
    exact add_equiv (hh _ 0 (by omega) (Or.inl rfl)) (neg_equiv (hh _ 4 (by omega) (Or.inr rfl)))
  · apply gridScalarSum_congr_bounded 4
    intro u hu
    exact add_equiv (hv 4 _ (Or.inr rfl) (by omega)) (neg_equiv (hv 0 _ (Or.inl rfl) (by omega)))

theorem outerBoundary_double_inner (f : QComplex → Scalar) (R : QPos) (M : Nat) (hM : 0<M) :
    outerBoundary f R M ≈ innerBoundary f (doubleContourRadius R) (2*M) := by
  let H := squareFrameHorizontalEdge f R M
  let V := squareFrameVerticalEdge f R M
  let A := squareFrameHorizontalEdge f (doubleContourRadius R) (2*M)
  let B := squareFrameVerticalEdge f (doubleContourRadius R) (2*M)
  have horizontal (a b : Nat) :
      gridScalarValue (H (2*a) (4*b))+gridScalarValue (H (2*a+1) (4*b))=
        gridScalarValue (A (a+1) (1+2*b)) :=
    ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (scalarSum (H (2*a) (4*b)) (H (2*a+1) (4*b))).property)
      (hright := (A (a+1) (1+2*b)).property) (doubleContour_horizontal_edge f R M a b hM)
  have vertical (a b : Nat) :
      gridScalarValue (V (4*b) (2*a))+gridScalarValue (V (4*b) (2*a+1))=
        gridScalarValue (B (1+2*b) (a+1)) :=
    ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (scalarSum (V (4*b) (2*a)) (V (4*b) (2*a+1))).property)
      (hright := (B (1+2*b) (a+1)).property) (doubleContour_vertical_edge f R M a b hM)
  have h00 := horizontal 0 0
  have h10 := horizontal 1 0
  have h01 := horizontal 0 1
  have h11 := horizontal 1 1
  have v00 := vertical 0 0
  have v10 := vertical 1 0
  have v01 := vertical 0 1
  have v11 := vertical 1 1
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (outerBoundary f R M).property) (hright := (innerBoundary f (doubleContourRadius R) (2*M)).property)
  change gridScalarValue (frameScalarRectBoundary H V 0 0 4 4)=
    gridScalarValue (frameScalarRectBoundary A B 1 1 2 2)
  rw [frameScalarRectBoundary_value,frameScalarRectBoundary_value]
  simp only [frameValueRectBoundary,gridValueBoundary,gridValueSum,Nat.zero_add]
  simp only [Nat.zero_mul,Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.one_add] at h00 h10 h01 h11 v00 v10 v01 v11
  grind only

end ComputableAnalysis.RiemannHilbert.RectangularContour
