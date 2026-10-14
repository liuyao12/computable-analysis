import ComputableAnalysis.RiemannHilbert.ContourRationalSums

/-! Exact comparison of the outer grid at one radius with the inner grid
at twice that radius. Every paired tile edge has the same midpoint samples. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def doubleContourRadius (R : QPos) : QPos :=
  ⟨2*R.val,Rat.mul_pos (by decide +kernel) R.property⟩

theorem doubleContour_grid_step (R : QPos) (M : Nat) :
    (doubleContourRadius R).val/((2*M:Nat):Rat)=R.val/(M:Rat) := by
  simp only [doubleContourRadius,Rat.natCast_mul,Rat.div_def,Rat.inv_mul_rev]
  change (2*R.val)*((M:Rat)⁻¹*(2:Rat)⁻¹)=R.val*(M:Rat)⁻¹
  grind only

theorem doubleContour_horizontal_point (R : QPos) (M a t b v : Nat) (hM : 0<M) :
    rectangleGridHorizontalPoint (squareFrameTile R (2*a+t) (4*b)) M v 0=
      rectangleGridHorizontalPoint (squareFrameTile (doubleContourRadius R) (a+1) (1+2*b))
        (2*M) (t*M+v) 0 := by
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have hi := Rat.mul_inv_cancel (M:Rat) hn
  unfold rectangleGridHorizontalPoint
  rw [(squareFrameTile_grid_steps R M _ _).1,(squareFrameTile_grid_steps R M _ _).2,
    (squareFrameTile_grid_steps (doubleContourRadius R) (2*M) _ _).1,
    (squareFrameTile_grid_steps (doubleContourRadius R) (2*M) _ _).2,doubleContour_grid_step]
  simp only [squareFrameTile,squareFrameInterval,doubleContourRadius,Rat.natCast_add,
    Rat.natCast_mul,Rat.div_def,QComplex.mk.injEq]
  change (-2*R.val+(2*(a:Rat)+(t:Rat))*R.val+((v:Rat)+1/2)*(R.val*(M:Rat)⁻¹)=
    -2*(2*R.val)+((a:Rat)+1)*(2*R.val)+((t:Rat)*(M:Rat)+(v:Rat)+1/2)*(R.val*(M:Rat)⁻¹)) ∧
    (-2*R.val+4*(b:Rat)*R.val+0*(R.val*(M:Rat)⁻¹)=
      -2*(2*R.val)+(1+2*(b:Rat))*(2*R.val)+0*(R.val*(M:Rat)⁻¹))
  constructor <;> grind only

theorem doubleContour_vertical_point (R : QPos) (M a t b v : Nat) (hM : 0<M) :
    rectangleGridVerticalPoint (squareFrameTile R (4*b) (2*a+t)) M 0 v=
      rectangleGridVerticalPoint (squareFrameTile (doubleContourRadius R) (1+2*b) (a+1))
        (2*M) 0 (t*M+v) := by
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have hi := Rat.mul_inv_cancel (M:Rat) hn
  unfold rectangleGridVerticalPoint
  rw [(squareFrameTile_grid_steps R M _ _).1,(squareFrameTile_grid_steps R M _ _).2,
    (squareFrameTile_grid_steps (doubleContourRadius R) (2*M) _ _).1,
    (squareFrameTile_grid_steps (doubleContourRadius R) (2*M) _ _).2,doubleContour_grid_step]
  simp only [squareFrameTile,squareFrameInterval,doubleContourRadius,Rat.natCast_add,
    Rat.natCast_mul,Rat.div_def,QComplex.mk.injEq]
  change (-2*R.val+4*(b:Rat)*R.val+0*(R.val*(M:Rat)⁻¹)=
    -2*(2*R.val)+(1+2*(b:Rat))*(2*R.val)+0*(R.val*(M:Rat)⁻¹)) ∧
    (-2*R.val+(2*(a:Rat)+(t:Rat))*R.val+((v:Rat)+1/2)*(R.val*(M:Rat)⁻¹)=
      -2*(2*R.val)+((a:Rat)+1)*(2*R.val)+((t:Rat)*(M:Rat)+(v:Rat)+1/2)*(R.val*(M:Rat)⁻¹))
  constructor <;> grind only

theorem doubleContour_horizontal_sample (f : QComplex → Scalar) (R : QPos)
    (M a t b v : Nat) (hM : 0<M) :
    rectangleGridHorizontal f (squareFrameTile R (2*a+t) (4*b)) M v 0=
      rectangleGridHorizontal f (squareFrameTile (doubleContourRadius R) (a+1) (1+2*b))
        (2*M) (t*M+v) 0 := by
  unfold rectangleGridHorizontal
  rw [doubleContour_horizontal_point R M a t b v hM,
    (squareFrameTile_grid_steps R M _ _).1,
    (squareFrameTile_grid_steps (doubleContourRadius R) (2*M) _ _).1,doubleContour_grid_step]

theorem doubleContour_vertical_sample (f : QComplex → Scalar) (R : QPos)
    (M a t b v : Nat) (hM : 0<M) :
    rectangleGridVertical f (squareFrameTile R (4*b) (2*a+t)) M 0 v=
      rectangleGridVertical f (squareFrameTile (doubleContourRadius R) (1+2*b) (a+1))
        (2*M) 0 (t*M+v) := by
  unfold rectangleGridVertical
  rw [doubleContour_vertical_point R M a t b v hM,
    (squareFrameTile_grid_steps R M _ _).2,
    (squareFrameTile_grid_steps (doubleContourRadius R) (2*M) _ _).2,doubleContour_grid_step]

theorem gridValueSum_concat (f : Nat → ScalarAlgebra.Value) (n m : Nat) :
    gridValueSum (n+m) f=gridValueSum n f+gridValueSum m (fun j => f (n+j)) := by
  induction m with
  | zero => simp only [Nat.add_zero,gridValueSum]; grind only
  | succ m ih =>
    rw [Nat.add_succ,gridValueSum,ih,gridValueSum]
    grind only

theorem gridScalarSum_concat (f : Nat → Scalar) (n m : Nat) :
    gridScalarSum (n+m) f ≈ scalarSum (gridScalarSum n f) (gridScalarSum m (fun j => f (n+j))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum (n+m) f).property)
    (hright := (scalarSum (gridScalarSum n f) (gridScalarSum m (fun j => f (n+j)))).property)
  change gridScalarValue (gridScalarSum (n+m) f)=
    gridScalarValue (gridScalarSum n f)+gridScalarValue (gridScalarSum m (fun j => f (n+j)))
  simp only [gridScalarSum_value]
  exact gridValueSum_concat _ n m

theorem doubleContour_horizontal_edge (f : QComplex → Scalar) (R : QPos)
    (M a b : Nat) (hM : 0<M) :
    scalarSum (squareFrameHorizontalEdge f R M (2*a) (4*b))
      (squareFrameHorizontalEdge f R M (2*a+1) (4*b)) ≈
      squareFrameHorizontalEdge f (doubleContourRadius R) (2*M) (a+1) (1+2*b) := by
  let term := fun v => rectangleGridHorizontal f
    (squareFrameTile (doubleContourRadius R) (a+1) (1+2*b)) (2*M) v 0
  have h0 := gridScalarSum_congr M
    (fun v => rectangleGridHorizontal f (squareFrameTile R (2*a) (4*b)) M v 0) term (by
    intro v
    have hs := doubleContour_horizontal_sample f R M a 0 b v hM
    simp only [Nat.add_zero,Nat.zero_mul,Nat.zero_add] at hs
    rw [hs]
    exact equiv_refl _ (term v).property)
  have h1 := gridScalarSum_congr M
    (fun v => rectangleGridHorizontal f (squareFrameTile R (2*a+1) (4*b)) M v 0)
    (fun v => term (M+v)) (by
    intro v
    rw [doubleContour_horizontal_sample f R M a 1 b v hM]
    simpa only [Nat.one_mul] using equiv_refl _ (term (M+v)).property)
  have hc := gridScalarSum_concat term M M
  have he : M+M=2*M := by omega
  rw [he] at hc
  exact Setoid.trans (add_equiv h0 h1) (Setoid.symm hc)

theorem doubleContour_vertical_edge (f : QComplex → Scalar) (R : QPos)
    (M a b : Nat) (hM : 0<M) :
    scalarSum (squareFrameVerticalEdge f R M (4*b) (2*a))
      (squareFrameVerticalEdge f R M (4*b) (2*a+1)) ≈
      squareFrameVerticalEdge f (doubleContourRadius R) (2*M) (1+2*b) (a+1) := by
  let term := fun v => rectangleGridVertical f
    (squareFrameTile (doubleContourRadius R) (1+2*b) (a+1)) (2*M) 0 v
  have h0 := gridScalarSum_congr M
    (fun v => rectangleGridVertical f (squareFrameTile R (4*b) (2*a)) M 0 v) term (by
    intro v
    have hs := doubleContour_vertical_sample f R M a 0 b v hM
    simp only [Nat.add_zero,Nat.zero_mul,Nat.zero_add] at hs
    rw [hs]
    exact equiv_refl _ (term v).property)
  have h1 := gridScalarSum_congr M
    (fun v => rectangleGridVertical f (squareFrameTile R (4*b) (2*a+1)) M 0 v)
    (fun v => term (M+v)) (by
    intro v
    rw [doubleContour_vertical_sample f R M a 1 b v hM]
    simpa only [Nat.one_mul] using equiv_refl _ (term (M+v)).property)
  have hc := gridScalarSum_concat term M M
  have he : M+M=2*M := by omega
  rw [he] at hc
  exact Setoid.trans (add_equiv h0 h1) (Setoid.symm hc)

end ComputableAnalysis.RiemannHilbert.RectangularContour
