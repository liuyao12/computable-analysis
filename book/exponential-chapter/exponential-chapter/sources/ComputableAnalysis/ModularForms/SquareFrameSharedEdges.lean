import ComputableAnalysis.ModularForms.PuncturedSquareFrameTiles

/-! Literal edge agreement for adjacent square-frame tiles. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem squareFrameTile_grid_steps (R : QPos) (M j k : Nat) :
    rectangleGridStepX (squareFrameTile R j k) M=R.val/(M:Rat) ∧
      rectangleGridStepY (squareFrameTile R j k) M=R.val/(M:Rat) := by
  simp only [rectangleGridStepX,rectangleGridStepY,squareFrameTile,squareFrameInterval,
    QInterval.width,Rat.natCast_add]
  change ((-2*R.val+((j:Rat)+1)*R.val)-(-2*R.val+(j:Rat)*R.val))/(M:Rat)=_ ∧
    ((-2*R.val+((k:Rat)+1)*R.val)-(-2*R.val+(k:Rat)*R.val))/(M:Rat)=_
  constructor <;> congr 1 <;> grind only

theorem squareFrameTile_shared_horizontal_points (R : QPos) (M j k u : Nat) (hM : 0<M) :
    rectangleGridHorizontalPoint (squareFrameTile R j k) M u M=
      rectangleGridHorizontalPoint (squareFrameTile R j (k+1)) M u 0 := by
  have hs := squareFrameTile_grid_steps R M j k
  have ht := squareFrameTile_grid_steps R M j (k+1)
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridHorizontalPoint
  rw [hs.1,hs.2,ht.1,ht.2]
  simp only [squareFrameTile,squareFrameInterval,QComplex.mk.injEq,Rat.natCast_add]
  change True ∧ -2*R.val+(k:Rat)*R.val+(M:Rat)*(R.val/(M:Rat))=
    -2*R.val+((k:Rat)+1)*R.val+0*(R.val/(M:Rat))
  constructor
  · trivial
  · rw [he]; grind only

theorem squareFrameTile_shared_vertical_points (R : QPos) (M j k u : Nat) (hM : 0<M) :
    rectangleGridVerticalPoint (squareFrameTile R j k) M M u=
      rectangleGridVerticalPoint (squareFrameTile R (j+1) k) M 0 u := by
  have hs := squareFrameTile_grid_steps R M j k
  have ht := squareFrameTile_grid_steps R M (j+1) k
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridVerticalPoint
  rw [hs.1,hs.2,ht.1,ht.2]
  simp only [squareFrameTile,squareFrameInterval,QComplex.mk.injEq,Rat.natCast_add]
  change -2*R.val+(j:Rat)*R.val+(M:Rat)*(R.val/(M:Rat))=
    -2*R.val+((j:Rat)+1)*R.val+0*(R.val/(M:Rat)) ∧ True
  constructor
  · rw [he]; grind only
  · trivial

theorem squareFrameTile_shared_horizontal_samples (f : QComplex → Scalar)
    (R : QPos) (M j k u : Nat) (hM : 0<M) :
    rectangleGridHorizontal f (squareFrameTile R j k) M u M=
      rectangleGridHorizontal f (squareFrameTile R j (k+1)) M u 0 := by
  unfold rectangleGridHorizontal
  rw [squareFrameTile_shared_horizontal_points R M j k u hM,
    (squareFrameTile_grid_steps R M j k).1,
    (squareFrameTile_grid_steps R M j (k+1)).1]

theorem squareFrameTile_shared_vertical_samples (f : QComplex → Scalar)
    (R : QPos) (M j k u : Nat) (hM : 0<M) :
    rectangleGridVertical f (squareFrameTile R j k) M M u=
      rectangleGridVertical f (squareFrameTile R (j+1) k) M 0 u := by
  unfold rectangleGridVertical
  rw [squareFrameTile_shared_vertical_points R M j k u hM,
    (squareFrameTile_grid_steps R M j k).2,
    (squareFrameTile_grid_steps R M (j+1) k).2]

def squareFrameHorizontalEdge (f : QComplex → Scalar) (R : QPos) (M j k : Nat) : Scalar :=
  gridScalarSum M (fun u => rectangleGridHorizontal f (squareFrameTile R j k) M u 0)

def squareFrameVerticalEdge (f : QComplex → Scalar) (R : QPos) (M j k : Nat) : Scalar :=
  gridScalarSum M (fun u => rectangleGridVertical f (squareFrameTile R j k) M 0 u)

theorem squareFrameTile_boundary_cell_agreement (f : QComplex → Scalar)
    (R : QPos) (M j k : Nat) (hM : 0<M) :
    (rectangleGridBoundary f (squareFrameTile R j k) M).val.Equiv
      (gridScalarCell (squareFrameHorizontalEdge f R M) (squareFrameVerticalEdge f R M) j k).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (rectangleGridBoundary f (squareFrameTile R j k) M).property)
    (hright := (gridScalarCell (squareFrameHorizontalEdge f R M) (squareFrameVerticalEdge f R M) j k).property)
  change gridScalarValue (rectangleGridBoundary f (squareFrameTile R j k) M)=
    gridScalarValue (gridScalarCell _ _ j k)
  simp only [rectangleGridBoundary,gridScalarBoundary,gridScalarCell,
    gridScalarValue_add,gridScalarValue_sub,squareFrameHorizontalEdge,squareFrameVerticalEdge,
    gridScalarSum_value,gridValueSum_sub]
  have hh : ∀ u, rectangleGridHorizontal f (squareFrameTile R j k) M u M=
      rectangleGridHorizontal f (squareFrameTile R j (k+1)) M u 0 :=
    fun u => squareFrameTile_shared_horizontal_samples f R M j k u hM
  have hv : ∀ u, rectangleGridVertical f (squareFrameTile R j k) M M u=
      rectangleGridVertical f (squareFrameTile R (j+1) k) M 0 u :=
    fun u => squareFrameTile_shared_vertical_samples f R M j k u hM
  simp only [hh,hv]

theorem frameScalarSum_congr (f g : Nat → Nat → Scalar) (l p r b q t : Nat)
    (h : ∀ j k, (f j k).val.Equiv (g j k).val) :
    (frameScalarSum f l p r b q t).val.Equiv (frameScalarSum g l p r b q t).val := by
  have hr (x y m n : Nat) : (frameScalarRectSum f x y m n).val.Equiv
      (frameScalarRectSum g x y m n).val :=
    gridScalarSum_congr m _ _ (fun j => gridScalarSum_congr n _ _ (fun k => h (x+j) (y+k)))
  exact add_equiv (add_equiv (hr _ _ _ _) (hr _ _ _ _))
    (add_equiv (hr _ _ _ _) (hr _ _ _ _))

theorem squareFrame_tiled_boundary_agreement (f : QComplex → Scalar)
    (R : QPos) (M : Nat) (hM : 0<M) :
    (frameScalarSum (fun j k => rectangleGridBoundary f (squareFrameTile R j k) M) 1 2 1 1 2 1).val.Equiv
      (gridScalarSub
        (frameScalarRectBoundary (squareFrameHorizontalEdge f R M) (squareFrameVerticalEdge f R M) 0 0 4 4)
        (frameScalarRectBoundary (squareFrameHorizontalEdge f R M) (squareFrameVerticalEdge f R M) 1 1 2 2)).val := by
  have he := frameScalarSum_congr
    (fun j k => rectangleGridBoundary f (squareFrameTile R j k) M)
    (gridScalarCell (squareFrameHorizontalEdge f R M) (squareFrameVerticalEdge f R M))
    1 2 1 1 2 1 (fun j k => squareFrameTile_boundary_cell_agreement f R M j k hM)
  exact equiv_trans (frameScalarSum (fun j k => rectangleGridBoundary f (squareFrameTile R j k) M) 1 2 1 1 2 1).property
    (frameScalarSum (gridScalarCell (squareFrameHorizontalEdge f R M) (squareFrameVerticalEdge f R M)) 1 2 1 1 2 1).property
    (gridScalarSub (frameScalarRectBoundary (squareFrameHorizontalEdge f R M) (squareFrameVerticalEdge f R M) 0 0 4 4)
      (frameScalarRectBoundary (squareFrameHorizontalEdge f R M) (squareFrameVerticalEdge f R M) 1 1 2 2)).property he (representedGrid_frame_stokes _ _ 1 2 1 1 2 1)

def puncturedKernel_squareFrameContourDifference (c : Scalar) (R : QPos) (n : Nat) : Scalar :=
  gridScalarSub
    (frameScalarRectBoundary (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R (2^n))
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R (2^n)) 0 0 4 4)
    (frameScalarRectBoundary (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R (2^n))
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R (2^n)) 1 1 2 2)

theorem puncturedKernel_squareFrameContourDifference_converges_zero (c : Scalar) (R eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (puncturedKernel_squareFrameContourDifference c R n).val eps.val := by
  obtain ⟨N,hN⟩ := puncturedKernel_squareFrameBoundarySum_converges_zero c R eps
  refine ⟨N, ?_⟩
  intro n hn
  exact Small.congr (puncturedKernel_squareFrameBoundarySum c R n).property
    (puncturedKernel_squareFrameContourDifference c R n).property
    (squareFrame_tiled_boundary_agreement (rationalRiccatiKernelSample c) R (2^n)
      (Nat.pow_pos (by decide))) (hN n hn)

end ComputableAnalysis.ModularForms



