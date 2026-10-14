import ComputableAnalysis.RiemannHilbert.ContourWeightedSamples

/-! Forward inner-square half-edge comparisons. Generic finite proofs adapted from the corresponding
`ModularForms` files; those original files are preserved. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

theorem common_inner_right_upper_sample (f : QComplex → Scalar) (R : QPos)
    (M v : Nat) (hM : 0<M) :
    (rectangleGridVertical f (squareFrameTile R 3 2) M 0 v).val.Equiv
      (scaleRat (1/(M:Rat)) (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.east,true⟩ (squareMidpointParameter M v))))
        (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.east,true⟩)))).val) := by
  rw [←squareFrameTile_shared_vertical_samples f R M 2 2 v hM]
  unfold rectangleGridVertical
  rw [squareFrame_inner_right_point R M 2 v hM,(squareFrameTile_grid_steps R M 2 2).2]
  have hp : ((2:Nat):Rat)-2+((v:Rat)+1/2)/(M:Rat)=squareMidpointParameter M v := by
    rw [show ((2:Nat):Rat)=(2:Rat) by decide +kernel]
    simp only [squareMidpointParameter,Rat.sub_self,Rat.zero_add]
  rw [hp,cartesianSquarePoint_agreement]
  have hw : (⟨0,R.val/(M:Rat)⟩ : QComplex)=QComplex.scaleRat (1/(M:Rat)) ⟨0,R.val⟩ := by
    simp only [QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  have hv : QComplex.scaleRat R.val (velocity ⟨.east,true⟩)=⟨0,R.val⟩ := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,
      Rat.mul_zero,Rat.mul_one,Rat.sub_self,Rat.add_zero]
  rw [hv]
  exact rationalWeightedSample_scale _ _ _

theorem common_inner_right_upper_average (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (squareFrameVerticalEdge f R M 3 2).val.Equiv
      (commonSquareKernelAverage f ⟨.east,true⟩ R M).val := by
  let density := fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point ⟨.east,true⟩ (squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.east,true⟩)))
  have hs := gridScalarSum_congr M _
    (fun v => (⟨scaleRat (1/(M:Rat)) (density v).val,scaleRat_valid (density v).property⟩ : Scalar))
    (fun v => common_inner_right_upper_sample f R M v hM)
  exact equiv_trans (squareFrameVerticalEdge f R M 3 2).property
    (gridScalarSum M (fun v => (⟨scaleRat (1/(M:Rat)) (density v).val,
      scaleRat_valid (density v).property⟩ : Scalar))).property
    (commonSquareKernelAverage f ⟨.east,true⟩ R M).property hs
    (gridScalarSum_scale (1/(M:Rat)) density M)

theorem common_inner_bottom_upper_sample (f : QComplex → Scalar) (R : QPos)
    (M v : Nat) (hM : 0<M) :
    (rectangleGridHorizontal f (squareFrameTile R 2 1) M v 0).val.Equiv
      (scaleRat (1/(M:Rat)) (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.south,true⟩ (squareMidpointParameter M v))))
        (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.south,true⟩)))).val) := by
  unfold rectangleGridHorizontal
  rw [squareFrame_inner_bottom_point R M 2 v hM,(squareFrameTile_grid_steps R M 2 1).1]
  have hp : ((2:Nat):Rat)-2+((v:Rat)+1/2)/(M:Rat)=squareMidpointParameter M v := by
    rw [show ((2:Nat):Rat)=(2:Rat) by decide +kernel]
    simp only [squareMidpointParameter,Rat.sub_self,Rat.zero_add]
  rw [hp,cartesianSquarePoint_agreement]
  have hw : (⟨R.val/(M:Rat),0⟩ : QComplex)=QComplex.scaleRat (1/(M:Rat)) ⟨R.val,0⟩ := by
    simp only [QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  have hv : QComplex.scaleRat R.val (velocity ⟨.south,true⟩)=⟨R.val,0⟩ := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,
      Rat.mul_zero,Rat.mul_one,Rat.sub_self,Rat.add_zero,Rat.sub_eq_add_neg,Rat.neg_neg,Rat.zero_add]
  rw [hv]
  exact rationalWeightedSample_scale _ _ _

theorem common_inner_bottom_upper_average (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (squareFrameHorizontalEdge f R M 2 1).val.Equiv
      (commonSquareKernelAverage f ⟨.south,true⟩ R M).val := by
  let density := fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point ⟨.south,true⟩ (squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.south,true⟩)))
  have hs := gridScalarSum_congr M _
    (fun v => (⟨scaleRat (1/(M:Rat)) (density v).val,scaleRat_valid (density v).property⟩ : Scalar))
    (fun v => common_inner_bottom_upper_sample f R M v hM)
  exact equiv_trans (squareFrameHorizontalEdge f R M 2 1).property
    (gridScalarSum M (fun v => (⟨scaleRat (1/(M:Rat)) (density v).val,
      scaleRat_valid (density v).property⟩ : Scalar))).property
    (commonSquareKernelAverage f ⟨.south,true⟩ R M).property hs
    (gridScalarSum_scale (1/(M:Rat)) density M)

end ComputableAnalysis.RiemannHilbert.RectangularContour
