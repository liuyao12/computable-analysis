import ComputableAnalysis.RiemannHilbert.ContourDisplacedCenters
import ComputableAnalysis.RiemannHilbert.ContourBoundarySampler
import ComputableAnalysis.RiemannHilbert.ContourRadiusConcatenation

/-! A rationally translated square has exactly the same midpoint samples as
the eight half edges of the inner frame, with twice as many full-edge cells. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem rationalCenteredRectangle_ordered (c : QComplex) (R : QPos) :
    (rationalCenteredRectangle c R.val).1.lo≤(rationalCenteredRectangle c R.val).1.hi ∧
    (rationalCenteredRectangle c R.val).2.lo≤(rationalCenteredRectangle c R.val).2.hi := by
  have hp := R.property
  change c.re-R.val≤c.re+R.val ∧ c.im-R.val≤c.im+R.val
  constructor <;> grind only

theorem rationalCenteredRectangle_grid_steps (c : QComplex) (R : QPos) (M : Nat) :
    rectangleGridStepX (rationalCenteredRectangle c R.val) (2*M)=R.val/(M:Rat) ∧
    rectangleGridStepY (rationalCenteredRectangle c R.val) (2*M)=R.val/(M:Rat) := by
  have hw (x : Rat) : (x+R.val)-(x-R.val)=2*R.val := by grind only
  simp only [rectangleGridStepX,rectangleGridStepY,rationalCenteredRectangle,QInterval.width,hw,
    Rat.natCast_mul,Rat.div_def,Rat.inv_mul_rev]
  change (2*R.val)*((M:Rat)⁻¹*(2:Rat)⁻¹)=R.val*(M:Rat)⁻¹ ∧
    (2*R.val)*((M:Rat)⁻¹*(2:Rat)⁻¹)=R.val*(M:Rat)⁻¹
  constructor <;> grind only

theorem rationalCenteredRectangle_horizontal_point (c : QComplex) (R : QPos)
    (M t k v : Nat) (hM : 0<M) :
    rectangleGridHorizontalPoint (rationalCenteredRectangle c R.val) (2*M) (t*M+v) (2*M*k)=
      QComplex.add c (rectangleGridHorizontalPoint (squareFrameTile R (1+t) (1+2*k)) M v 0) := by
  have hi := Rat.mul_inv_cancel (M:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  unfold rectangleGridHorizontalPoint
  rw [(rationalCenteredRectangle_grid_steps c R M).1,(rationalCenteredRectangle_grid_steps c R M).2,
    (squareFrameTile_grid_steps R M _ _).1,(squareFrameTile_grid_steps R M _ _).2]
  simp only [rationalCenteredRectangle,squareFrameTile,squareFrameInterval,QComplex.add,
    Rat.natCast_add,Rat.natCast_mul,Rat.div_def,QComplex.mk.injEq]
  change (c.re-R.val+((t:Rat)*(M:Rat)+(v:Rat)+1/2)*(R.val*(M:Rat)⁻¹)=
    c.re+(-2*R.val+(1+(t:Rat))*R.val+((v:Rat)+1/2)*(R.val*(M:Rat)⁻¹))) ∧
    (c.im-R.val+2*(M:Rat)*(k:Rat)*(R.val*(M:Rat)⁻¹)=
      c.im+(-2*R.val+(1+2*(k:Rat))*R.val+0*(R.val*(M:Rat)⁻¹)))
  constructor <;> grind only

theorem rationalCenteredRectangle_vertical_point (c : QComplex) (R : QPos)
    (M t k v : Nat) (hM : 0<M) :
    rectangleGridVerticalPoint (rationalCenteredRectangle c R.val) (2*M) (2*M*k) (t*M+v)=
      QComplex.add c (rectangleGridVerticalPoint (squareFrameTile R (1+2*k) (1+t)) M 0 v) := by
  have hi := Rat.mul_inv_cancel (M:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  unfold rectangleGridVerticalPoint
  rw [(rationalCenteredRectangle_grid_steps c R M).1,(rationalCenteredRectangle_grid_steps c R M).2,
    (squareFrameTile_grid_steps R M _ _).1,(squareFrameTile_grid_steps R M _ _).2]
  simp only [rationalCenteredRectangle,squareFrameTile,squareFrameInterval,QComplex.add,
    Rat.natCast_add,Rat.natCast_mul,Rat.div_def,QComplex.mk.injEq]
  change (c.re-R.val+2*(M:Rat)*(k:Rat)*(R.val*(M:Rat)⁻¹)=
    c.re+(-2*R.val+(1+2*(k:Rat))*R.val+0*(R.val*(M:Rat)⁻¹))) ∧
    (c.im-R.val+((t:Rat)*(M:Rat)+(v:Rat)+1/2)*(R.val*(M:Rat)⁻¹)=
      c.im+(-2*R.val+(1+(t:Rat))*R.val+((v:Rat)+1/2)*(R.val*(M:Rat)⁻¹)))
  constructor <;> grind only

theorem rationalCenteredRectangle_horizontal_sample (s : QComplex → Scalar) (c : QComplex) (R : QPos)
    (M t k v : Nat) (hM : 0<M) :
    rectangleGridHorizontal s (rationalCenteredRectangle c R.val) (2*M) (t*M+v) (2*M*k)=
      rectangleGridHorizontal (fun q => s (QComplex.add c q)) (squareFrameTile R (1+t) (1+2*k)) M v 0 := by
  unfold rectangleGridHorizontal
  rw [rationalCenteredRectangle_horizontal_point c R M t k v hM,
    (rationalCenteredRectangle_grid_steps c R M).1,(squareFrameTile_grid_steps R M _ _).1]

theorem rationalCenteredRectangle_vertical_sample (s : QComplex → Scalar) (c : QComplex) (R : QPos)
    (M t k v : Nat) (hM : 0<M) :
    rectangleGridVertical s (rationalCenteredRectangle c R.val) (2*M) (2*M*k) (t*M+v)=
      rectangleGridVertical (fun q => s (QComplex.add c q)) (squareFrameTile R (1+2*k) (1+t)) M 0 v := by
  unfold rectangleGridVertical
  rw [rationalCenteredRectangle_vertical_point c R M t k v hM,
    (rationalCenteredRectangle_grid_steps c R M).2,(squareFrameTile_grid_steps R M _ _).2]

theorem rationalCenteredRectangle_horizontal_edge (s : QComplex → Scalar) (c : QComplex) (R : QPos)
    (M k : Nat) (hM : 0<M) :
    gridScalarSum (2*M) (fun v => rectangleGridHorizontal s (rationalCenteredRectangle c R.val) (2*M) v (2*M*k))≈
      scalarSum (squareFrameHorizontalEdge (fun q => s (QComplex.add c q)) R M 1 (1+2*k))
        (squareFrameHorizontalEdge (fun q => s (QComplex.add c q)) R M 2 (1+2*k)) := by
  let term := fun v => rectangleGridHorizontal s (rationalCenteredRectangle c R.val) (2*M) v (2*M*k)
  have h0 := gridScalarSum_congr M term
    (fun v => rectangleGridHorizontal (fun q => s (QComplex.add c q)) (squareFrameTile R 1 (1+2*k)) M v 0) (by
    intro v
    have he := rationalCenteredRectangle_horizontal_sample s c R M 0 k v hM
    dsimp [term]
    simp only [Nat.zero_mul,Nat.zero_add] at he
    rw [he]
    exact equiv_refl _ (rectangleGridHorizontal _ _ _ _ _).property)
  have h1 := gridScalarSum_congr M (fun v => term (M+v))
    (fun v => rectangleGridHorizontal (fun q => s (QComplex.add c q)) (squareFrameTile R 2 (1+2*k)) M v 0) (by
    intro v
    have he := rationalCenteredRectangle_horizontal_sample s c R M 1 k v hM
    simp only [Nat.one_mul] at he
    dsimp [term]
    rw [he]
    exact equiv_refl _ (rectangleGridHorizontal _ _ _ _ _).property)
  have hc := gridScalarSum_concat term M M
  have he : M+M=2*M := by omega
  rw [he] at hc
  exact Setoid.trans hc (add_equiv h0 h1)

theorem rationalCenteredRectangle_vertical_edge (s : QComplex → Scalar) (c : QComplex) (R : QPos)
    (M k : Nat) (hM : 0<M) :
    gridScalarSum (2*M) (fun v => rectangleGridVertical s (rationalCenteredRectangle c R.val) (2*M) (2*M*k) v)≈
      scalarSum (squareFrameVerticalEdge (fun q => s (QComplex.add c q)) R M (1+2*k) 1)
        (squareFrameVerticalEdge (fun q => s (QComplex.add c q)) R M (1+2*k) 2) := by
  let term := fun v => rectangleGridVertical s (rationalCenteredRectangle c R.val) (2*M) (2*M*k) v
  have h0 := gridScalarSum_congr M term
    (fun v => rectangleGridVertical (fun q => s (QComplex.add c q)) (squareFrameTile R (1+2*k) 1) M 0 v) (by
    intro v
    have he := rationalCenteredRectangle_vertical_sample s c R M 0 k v hM
    simp only [Nat.zero_mul,Nat.zero_add] at he
    dsimp [term]
    rw [he]
    exact equiv_refl _ (rectangleGridVertical _ _ _ _ _).property)
  have h1 := gridScalarSum_congr M (fun v => term (M+v))
    (fun v => rectangleGridVertical (fun q => s (QComplex.add c q)) (squareFrameTile R (1+2*k) 2) M 0 v) (by
    intro v
    have he := rationalCenteredRectangle_vertical_sample s c R M 1 k v hM
    simp only [Nat.one_mul] at he
    dsimp [term]
    rw [he]
    exact equiv_refl _ (rectangleGridVertical _ _ _ _ _).property)
  have hc := gridScalarSum_concat term M M
  have he : M+M=2*M := by omega
  rw [he] at hc
  exact Setoid.trans hc (add_equiv h0 h1)

theorem frameScalarRectBoundary_two_edges (h v : Nat → Nat → Scalar) :
    frameScalarRectBoundary h v 1 1 2 2≈scalarSum
      (gridScalarSub (scalarSum (h 1 1) (h 2 1)) (scalarSum (h 1 3) (h 2 3)))
      (gridScalarSub (scalarSum (v 3 1) (v 3 2)) (scalarSum (v 1 1) (v 1 2))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (frameScalarRectBoundary h v 1 1 2 2).property)
    (hright := (scalarSum _ _).property)
  change gridScalarValue (frameScalarRectBoundary h v 1 1 2 2)=gridScalarValue (scalarSum _ _)
  simp only [frameScalarRectBoundary,gridScalarBoundary,gridScalarValue_add,
    gridScalarSum_value,gridScalarValue_sub,gridValueSum]
  grind only

theorem innerBoundary_paired_edges (s : QComplex → Scalar) (R : QPos) (M : Nat) :
    innerBoundary s R M≈scalarSum
      (gridScalarSub (scalarSum (squareFrameHorizontalEdge s R M 1 1) (squareFrameHorizontalEdge s R M 2 1))
        (scalarSum (squareFrameHorizontalEdge s R M 1 3) (squareFrameHorizontalEdge s R M 2 3)))
      (gridScalarSub (scalarSum (squareFrameVerticalEdge s R M 3 1) (squareFrameVerticalEdge s R M 3 2))
        (scalarSum (squareFrameVerticalEdge s R M 1 1) (squareFrameVerticalEdge s R M 1 2))) :=
  frameScalarRectBoundary_two_edges (squareFrameHorizontalEdge s R M) (squareFrameVerticalEdge s R M)

theorem rationalCenteredRectangle_boundary (s : QComplex → Scalar) (c : QComplex) (R : QPos)
    (M : Nat) (hM : 0<M) :
    rectangleGridBoundary s (rationalCenteredRectangle c R.val) (2*M)≈
      innerBoundary (fun q => s (QComplex.add c q)) R M := by
  let J := rationalCenteredRectangle c R.val
  have hb := rationalCenteredRectangle_horizontal_edge s c R M 0 hM
  have ht := rationalCenteredRectangle_horizontal_edge s c R M 1 hM
  have hl := rationalCenteredRectangle_vertical_edge s c R M 0 hM
  have hr := rationalCenteredRectangle_vertical_edge s c R M 1 hM
  simp only [Nat.mul_zero,Nat.mul_one] at hb ht hl hr
  let t := fun q => s (QComplex.add c q)
  refine Setoid.trans (b := scalarSum
    (gridScalarSub (scalarSum (squareFrameHorizontalEdge t R M 1 1) (squareFrameHorizontalEdge t R M 2 1))
      (scalarSum (squareFrameHorizontalEdge t R M 1 3) (squareFrameHorizontalEdge t R M 2 3)))
    (gridScalarSub (scalarSum (squareFrameVerticalEdge t R M 3 1) (squareFrameVerticalEdge t R M 3 2))
      (scalarSum (squareFrameVerticalEdge t R M 1 1) (squareFrameVerticalEdge t R M 1 2)))) ?_ ?_
  · exact add_equiv
      (Setoid.trans (gridScalarSum_sub_agreement (2*M) (fun j => rectangleGridHorizontal s J (2*M) j 0)
        (fun j => rectangleGridHorizontal s J (2*M) j (2*M))) (FunctionTheory.sub_congr hb ht))
      (Setoid.trans (gridScalarSum_sub_agreement (2*M) (fun k => rectangleGridVertical s J (2*M) (2*M) k)
        (fun k => rectangleGridVertical s J (2*M) 0 k)) (FunctionTheory.sub_congr hr hl))
  · exact Setoid.symm (innerBoundary_paired_edges _ R M)

end ComputableAnalysis.RiemannHilbert.RectangularContour
