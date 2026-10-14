import ComputableAnalysis.RiemannHilbert.ContourInverseBounds
import ComputableAnalysis.RiemannHilbert.ContourBoundaryAgreement

/-! Every rational midpoint on the inner boundary belongs to the actual
frame, including the sides sampled from a nominal central tile. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions BoxApproximation
set_option autoImplicit false

def innerHorizontalPoint (R : QPos) (M j k u : Nat) : QComplex :=
  rectangleGridHorizontalPoint (squareFrameTile R j k) M u 0

def innerVerticalPoint (R : QPos) (M j k u : Nat) : QComplex :=
  rectangleGridVerticalPoint (squareFrameTile R j k) M 0 u

theorem innerHorizontalPoint_mem (R : QPos) (M j k u : Nat) (hM : 0<M)
    (hj : j=1 ∨ j=2) (hk : k=1 ∨ k=3) (hu : u<M) :
    frameDomain R (rationalRectangleScalar (innerHorizontalPoint R M j k u)) := by
  rcases hk with hk|hk
  · subst k
    unfold innerHorizontalPoint
    rw [←squareFrameTile_shared_horizontal_points R M j 0 u hM]
    have ho := squareFrameTile_ordered R j 0
    exact ⟨j,0,by unfold squareFrameTileIndex; omega,
      rationalRectangle_represented_mem _ _
        (rectangleGridHorizontalPoint_mem _ M u M ho.1 ho.2 hM hu (Nat.le_refl M))⟩
  · subst k
    have ho := squareFrameTile_ordered R j 3
    exact ⟨j,3,by unfold squareFrameTileIndex; omega,
      rationalRectangle_represented_mem _ _
        (rectangleGridHorizontalPoint_mem _ M u 0 ho.1 ho.2 hM hu (Nat.zero_le M))⟩

theorem innerVerticalPoint_mem (R : QPos) (M j k u : Nat) (hM : 0<M)
    (hj : j=1 ∨ j=3) (hk : k=1 ∨ k=2) (hu : u<M) :
    frameDomain R (rationalRectangleScalar (innerVerticalPoint R M j k u)) := by
  rcases hj with hj|hj
  · subst j
    unfold innerVerticalPoint
    rw [←squareFrameTile_shared_vertical_points R M 0 k u hM]
    have ho := squareFrameTile_ordered R 0 k
    exact ⟨0,k,by unfold squareFrameTileIndex; omega,
      rationalRectangle_represented_mem _ _
        (rectangleGridVerticalPoint_mem _ M M u ho.1 ho.2 hM (Nat.le_refl M) hu)⟩
  · subst j
    have ho := squareFrameTile_ordered R 3 k
    exact ⟨3,k,by unfold squareFrameTileIndex; omega,
      rationalRectangle_represented_mem _ _
        (rectangleGridVerticalPoint_mem _ M 0 u ho.1 ho.2 hM (Nat.zero_le M) hu)⟩

theorem frameHorizontal_velocity_bound (R : QPos) (M j k : Nat) (hM : 0<M) :
    Small (rationalRectangleScalar ⟨rectangleGridStepX (squareFrameTile R j k) M,0⟩).val
      (R.val/(M:Rat)) := by
  rw [(squareFrameTile_grid_steps R M j k).1]
  have hs : 0≤R.val/(M:Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt R.property)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hM)))
  have hb : coordinateBound ⟨R.val/(M:Rat),0⟩≤R.val/(M:Rat) := by
    unfold coordinateBound qabs
    grind
  exact (rational_small _).mono hb

theorem frameVertical_velocity_bound (R : QPos) (M j k : Nat) (hM : 0<M) :
    Small (rationalRectangleScalar ⟨0,rectangleGridStepY (squareFrameTile R j k) M⟩).val
      (R.val/(M:Rat)) := by
  rw [(squareFrameTile_grid_steps R M j k).2]
  have hs : 0≤R.val/(M:Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt R.property)
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hM)))
  have hb : coordinateBound ⟨0,R.val/(M:Rat)⟩≤R.val/(M:Rat) := by
    unfold coordinateBound qabs
    grind
  exact (rational_small _).mono hb

def innerBoundary (sample : QComplex → Scalar) (R : QPos) (M : Nat) : Scalar :=
  frameScalarRectBoundary (squareFrameHorizontalEdge sample R M) (squareFrameVerticalEdge sample R M) 1 1 2 2

end ComputableAnalysis.RiemannHilbert.RectangularContour
