import ComputableAnalysis.ModularForms.SquareFrameSharedEdges
import ComputableAnalysis.ModularForms.PairedRiccatiSquareDensityAgreement
import ComputableAnalysis.ModularForms.PairedSquareDensityDyadicCauchy

/-! Cartesian geometry and literal kernel samples for the existing half-edge densities. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

def cartesianSquarePoint (edge : HalfEdge) (R u : Rat) : QComplex :=
  let t := orientation edge*R*u
  match edge.quarter with
  | .east => ⟨R,t⟩
  | .north => ⟨-t,R⟩
  | .west => ⟨-R,-t⟩
  | .south => ⟨t,-R⟩

theorem cartesianSquarePoint_agreement (edge : HalfEdge) (R u : Rat) :
    cartesianSquarePoint edge R u=QComplex.scaleRat R (point edge u) := by
  cases edge with
  | mk q b =>
    cases q <;> cases b <;>
      simp only [cartesianSquarePoint,point,orientation,rotation,QComplex.mul,QComplex.scaleRat,
        Bool.false_eq_true,↓reduceIte,QComplex.mk.injEq] <;>
      constructor <;> grind only

/-- The literal oriented kernel product used at each half-edge sample. -/
def cartesianSquareKernelDensity (c : Scalar) (edge : HalfEdge) (R u : Rat) : Scalar :=
  let d := scalarProduct (rationalRiccatiKernelSample c (cartesianSquarePoint edge R u))
    (rationalRectangleScalar (QComplex.scaleRat R (velocity edge)))
  if edge.upper then d else scalarNeg d

theorem cartesianSquareKernelDensity_agreement (c : Scalar) (edge : HalfEdge) (R u : Rat) :
    (cartesianSquareKernelDensity c edge R u).val=(pairedSquareDensitySample c edge R u).val := by
  unfold cartesianSquareKernelDensity
  rw [cartesianSquarePoint_agreement]
  cases edge with
  | mk q b => cases b <;> rfl

theorem cartesianSquareKernelDensity_average_agreement (c : Scalar) (edge : HalfEdge)
    (R : Rat) (n : Nat) :
    (dyadicSampleAverage (cartesianSquareKernelDensity c edge R) ⟨0,1⟩ n).val.Equiv
      (pairedSquareDyadicAverage c edge R n).val := by
  have he : cartesianSquareKernelDensity c edge R=pairedSquareDensitySample c edge R := by
    funext u
    apply Subtype.ext
    exact cartesianSquareKernelDensity_agreement c edge R u
  rw [he]
  exact equiv_refl _ (pairedSquareDyadicAverage c edge R n).property

theorem squareFrame_outer_right_point (R : QPos) (M k v : Nat) (hM : 0<M) :
    rectangleGridVerticalPoint (squareFrameTile R 3 k) M M v=
      cartesianSquarePoint ⟨.east,true⟩ (2*R.val)
        (((k:Rat)-2+((v:Rat)+1/2)/(M:Rat))/2) := by
  have hs := squareFrameTile_grid_steps R M 3 k
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridVerticalPoint
  rw [hs.1,hs.2]
  simp only [squareFrameTile,squareFrameInterval,cartesianSquarePoint,orientation,
    ↓reduceIte,QComplex.mk.injEq]
  constructor
  · change -2*R.val+3*R.val+(M:Rat)*(R.val/(M:Rat))=2*R.val
    rw [he]; grind only
  · change -2*R.val+(k:Rat)*R.val+((v:Rat)+1/2)*(R.val/(M:Rat))=
      1*(2*R.val)*(((k:Rat)-2+((v:Rat)+1/2)/(M:Rat))/2)
    simp only [Rat.div_def]
    grind only

theorem squareFrame_outer_top_point (R : QPos) (M j v : Nat) (hM : 0<M) :
    rectangleGridHorizontalPoint (squareFrameTile R j 3) M v M=
      cartesianSquarePoint ⟨.north,true⟩ (2*R.val) ((2-(j:Rat)-((v:Rat)+1/2)/(M:Rat))/2) := by
  have hs := squareFrameTile_grid_steps R M j 3
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridHorizontalPoint
  rw [hs.1,hs.2]
  simp only [squareFrameTile,squareFrameInterval,cartesianSquarePoint,orientation,
    ↓reduceIte,QComplex.mk.injEq]
  simp only [Rat.div_def] at he ⊢
  constructor <;> grind only

theorem squareFrame_outer_left_point (R : QPos) (M k v : Nat) (hM : 0<M) :
    rectangleGridVerticalPoint (squareFrameTile R 0 k) M 0 v=
      cartesianSquarePoint ⟨.west,true⟩ (2*R.val) ((2-(k:Rat)-((v:Rat)+1/2)/(M:Rat))/2) := by
  have hs := squareFrameTile_grid_steps R M 0 k
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridVerticalPoint
  rw [hs.1,hs.2]
  simp only [squareFrameTile,squareFrameInterval,cartesianSquarePoint,orientation,
    ↓reduceIte,QComplex.mk.injEq]
  simp only [Rat.div_def] at he ⊢
  constructor <;> grind only

theorem squareFrame_outer_bottom_point (R : QPos) (M j v : Nat) (hM : 0<M) :
    rectangleGridHorizontalPoint (squareFrameTile R j 0) M v 0=
      cartesianSquarePoint ⟨.south,true⟩ (2*R.val) (((j:Rat)-2+((v:Rat)+1/2)/(M:Rat))/2) := by
  have hs := squareFrameTile_grid_steps R M j 0
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridHorizontalPoint
  rw [hs.1,hs.2]
  simp only [squareFrameTile,squareFrameInterval,cartesianSquarePoint,orientation,
    ↓reduceIte,QComplex.mk.injEq]
  simp only [Rat.div_def] at he ⊢
  constructor <;> grind only

end ComputableAnalysis.ModularForms

