import ComputableAnalysis.ModularForms.SquareContourCartesianGeometry

/-! Exact inner-square sample coordinates for the frame contour comparison. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squareFrame_inner_right_point (R : QPos) (M k v : Nat) (hM : 0<M) :
    rectangleGridVerticalPoint (squareFrameTile R 2 k) M M v=
      cartesianSquarePoint ⟨.east,true⟩ R.val ((k:Rat)-2+((v:Rat)+1/2)/(M:Rat)) := by
  have hs := squareFrameTile_grid_steps R M 2 k
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridVerticalPoint
  rw [hs.1,hs.2]
  simp only [squareFrameTile,squareFrameInterval,cartesianSquarePoint,orientation,
    ↓reduceIte,QComplex.mk.injEq]
  simp only [Rat.div_def] at he ⊢
  constructor <;> grind only

theorem squareFrame_inner_top_point (R : QPos) (M j v : Nat) (hM : 0<M) :
    rectangleGridHorizontalPoint (squareFrameTile R j 2) M v M=
      cartesianSquarePoint ⟨.north,true⟩ R.val (2-(j:Rat)-((v:Rat)+1/2)/(M:Rat)) := by
  have hs := squareFrameTile_grid_steps R M j 2
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridHorizontalPoint
  rw [hs.1,hs.2]
  simp only [squareFrameTile,squareFrameInterval,cartesianSquarePoint,orientation,
    ↓reduceIte,QComplex.mk.injEq]
  simp only [Rat.div_def] at he ⊢
  constructor <;> grind only

theorem squareFrame_inner_left_point (R : QPos) (M k v : Nat) (hM : 0<M) :
    rectangleGridVerticalPoint (squareFrameTile R 1 k) M 0 v=
      cartesianSquarePoint ⟨.west,true⟩ R.val (2-(k:Rat)-((v:Rat)+1/2)/(M:Rat)) := by
  have hs := squareFrameTile_grid_steps R M 1 k
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridVerticalPoint
  rw [hs.1,hs.2]
  simp only [squareFrameTile,squareFrameInterval,cartesianSquarePoint,orientation,
    ↓reduceIte,QComplex.mk.injEq]
  simp only [Rat.div_def] at he ⊢
  constructor <;> grind only

theorem squareFrame_inner_bottom_point (R : QPos) (M j v : Nat) (hM : 0<M) :
    rectangleGridHorizontalPoint (squareFrameTile R j 1) M v 0=
      cartesianSquarePoint ⟨.south,true⟩ R.val ((j:Rat)-2+((v:Rat)+1/2)/(M:Rat)) := by
  have hs := squareFrameTile_grid_steps R M j 1
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he : (M:Rat)*(R.val/(M:Rat))=R.val := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hn
  unfold rectangleGridHorizontalPoint
  rw [hs.1,hs.2]
  simp only [squareFrameTile,squareFrameInterval,cartesianSquarePoint,orientation,
    ↓reduceIte,QComplex.mk.injEq]
  simp only [Rat.div_def] at he ⊢
  constructor <;> grind only

theorem gridValueSum_head_shift (f : Nat → ScalarAlgebra.Value) (n : Nat) :
    gridValueSum (n+1) f=f 0+gridValueSum n (fun j => f (j+1)) := by
  induction n with
  | zero => simp only [gridValueSum]; grind only
  | succ n ih => simp only [gridValueSum] at ih ⊢; grind only

theorem gridValueSum_reverse (f : Nat → ScalarAlgebra.Value) (n : Nat) :
    gridValueSum n (fun j => f (n-1-j))=gridValueSum n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [gridValueSum_head_shift]
    have he : (fun j => f (n+1-1-(j+1)))=(fun j => f (n-1-j)) := by
      funext j
      congr 1
      omega
    rw [he,ih]
    simp only [gridValueSum]
    have hn : n+1-1-0=n := by omega
    rw [hn]
    grind only

theorem gridScalarSum_reverse (f : Nat → Scalar) (n : Nat) :
    (gridScalarSum n (fun j => f (n-1-j))).val.Equiv (gridScalarSum n f).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum n (fun j => f (n-1-j))).property)
    (hright := (gridScalarSum n f).property)
  change gridScalarValue (gridScalarSum n (fun j => f (n-1-j)))=
    gridScalarValue (gridScalarSum n f)
  simp only [gridScalarSum_value]
  exact gridValueSum_reverse (fun j => gridScalarValue (f j)) n

def squareMidpointParameter (M v : Nat) : Rat := ((v:Rat)+1/2)/(M:Rat)

theorem squareMidpointParameter_reverse (M v : Nat) (hM : 0<M) (hv : v<M) :
    squareMidpointParameter M (M-1-v)=1-squareMidpointParameter M v := by
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have hi : v+(M-1-v)+1=M := by omega
  have hc := congrArg (fun n : Nat => (n:Rat)) hi
  simp only [Rat.natCast_add] at hc
  have he := Rat.mul_inv_cancel (M:Rat) hn
  unfold squareMidpointParameter
  simp only [Rat.div_def]
  change (v:Rat)+((M-1-v:Nat):Rat)+1=(M:Rat) at hc
  grind only

theorem squareMidpointParameter_concat (M a v : Nat) (hM : 0<M) :
    ((a:Rat)+squareMidpointParameter M v)/2=
      squareMidpointParameter (2*M) (a*M+v) := by
  unfold squareMidpointParameter
  simp only [Rat.natCast_add,Rat.natCast_mul,Rat.div_def,Rat.inv_mul_rev]
  have hn : (M:Rat)≠0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hM)
  have he := Rat.mul_inv_cancel (M:Rat) hn
  change ((a:Rat)+((v:Rat)+1/2)*(M:Rat)⁻¹)*(2:Rat)⁻¹=
    ((a:Rat)*(M:Rat)+(v:Rat)+1/2)*((M:Rat)⁻¹*(2:Rat)⁻¹)
  grind only

end ComputableAnalysis.ModularForms
