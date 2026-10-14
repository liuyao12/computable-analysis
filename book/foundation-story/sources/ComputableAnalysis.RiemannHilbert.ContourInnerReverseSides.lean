import ComputableAnalysis.RiemannHilbert.ContourInnerSignedAverages

/-! Exact reflected top and left inner-square sides. Generic finite proofs adapted from the corresponding
`ModularForms` files; those original files are preserved. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

theorem common_inner_top_upper_sample (f : QComplex → Scalar) (R : QPos)
    (M v : Nat) (hM : 0<M) :
    (rectangleGridHorizontal f (squareFrameTile R 1 3) M v 0).val.Equiv
      (scaleRat (1/(M:Rat)) (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.north,true⟩ (1-squareMidpointParameter M v))))
        (rationalRectangleScalar ⟨R.val,0⟩)).val) := by
  rw [←squareFrameTile_shared_horizontal_samples f R M 1 2 v hM]
  unfold rectangleGridHorizontal
  rw [squareFrame_inner_top_point R M 1 v hM,(squareFrameTile_grid_steps R M 1 2).1]
  have hp : cartesianSquarePoint ⟨.north,true⟩ R.val
      (2-((1:Nat):Rat)-((v:Rat)+1/2)/(M:Rat))=
      QComplex.scaleRat R.val (point ⟨.north,true⟩ (1-squareMidpointParameter M v)) := by
    rw [show ((1:Nat):Rat)=(1:Rat) by decide +kernel]
    simp only [cartesianSquarePoint,point,rotation,orientation,squareMidpointParameter,
      Bool.false_eq_true,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  rw [hp]
  have hw : (⟨R.val/(M:Rat),0⟩ : QComplex)=QComplex.scaleRat (1/(M:Rat)) ⟨R.val,0⟩ := by
    simp only [QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  exact rationalWeightedSample_scale _ _ _

theorem common_inner_top_upper_average (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (squareFrameHorizontalEdge f R M 1 3).val.Equiv
      (neg (commonSquareKernelAverage f ⟨.north,true⟩ R M).val) := by
  let density := fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point ⟨.north,true⟩ (1-squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.north,true⟩)))
  have hv : QComplex.scaleRat R.val (velocity ⟨.north,true⟩)=
      QComplex.scaleRat (-1) (⟨R.val,0⟩ : QComplex) := by
    simp only [velocity,rotation,orientation,Bool.false_eq_true,↓reduceIte,
      QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  have he (v : Nat) : (rectangleGridHorizontal f (squareFrameTile R 1 3) M v 0).val.Equiv
      (scaleRat (-(1/(M:Rat))) (density v).val) := by
    have hs := common_inner_top_upper_sample f R M v hM
    have ht := weightedSample_signed_scale
      (f (QComplex.scaleRat R.val (point ⟨.north,true⟩ (1-squareMidpointParameter M v))))
      ⟨R.val,0⟩ (1/(M:Rat))
    rw [←hv] at ht
    exact equiv_trans (rectangleGridHorizontal f (squareFrameTile R 1 3) M v 0).property
      (scaleRat_valid (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.north,true⟩ (1-squareMidpointParameter M v))))
        (rationalRectangleScalar ⟨R.val,0⟩)).property)
      (scaleRat_valid (density v).property) hs ht
  let weighted := fun v => (⟨scaleRat (-(1/(M:Rat))) (density v).val,
    scaleRat_valid (density v).property⟩ : Scalar)
  have hs := gridScalarSum_congr M _ weighted he
  have ht := gridScalarSum_scale (-(1/(M:Rat))) density M
  have hn := negativeScale_equiv_negScale (gridScalarSum M density) (1/(M:Rat))
  have hr := neg_equiv (commonReflectedSquareAverage_agreement f ⟨.north,true⟩ R M hM)
  exact equiv_trans (squareFrameHorizontalEdge f R M 1 3).property
    (gridScalarSum M weighted).property
    (neg_valid (commonSquareKernelAverage f ⟨.north,true⟩ R M).property) hs
    (equiv_trans (gridScalarSum M weighted).property
      (scaleRat_valid (gridScalarSum M density).property)
      (neg_valid (commonSquareKernelAverage f ⟨.north,true⟩ R M).property) ht
      (equiv_trans (scaleRat_valid (gridScalarSum M density).property)
        (neg_valid (commonReflectedSquareAverage f ⟨.north,true⟩ R M).property)
        (neg_valid (commonSquareKernelAverage f ⟨.north,true⟩ R M).property) hn hr))

theorem common_inner_left_upper_sample (f : QComplex → Scalar) (R : QPos)
    (M v : Nat) (hM : 0<M) :
    (rectangleGridVertical f (squareFrameTile R 1 1) M 0 v).val.Equiv
      (scaleRat (1/(M:Rat)) (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.west,true⟩ (1-squareMidpointParameter M v))))
        (rationalRectangleScalar ⟨0,R.val⟩)).val) := by
  unfold rectangleGridVertical
  rw [squareFrame_inner_left_point R M 1 v hM,(squareFrameTile_grid_steps R M 1 1).2]
  have hp : cartesianSquarePoint ⟨.west,true⟩ R.val
      (2-((1:Nat):Rat)-((v:Rat)+1/2)/(M:Rat))=
      QComplex.scaleRat R.val (point ⟨.west,true⟩ (1-squareMidpointParameter M v)) := by
    rw [show ((1:Nat):Rat)=(1:Rat) by decide +kernel]
    simp only [cartesianSquarePoint,point,rotation,orientation,squareMidpointParameter,
      Bool.false_eq_true,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  rw [hp]
  have hw : (⟨0,R.val/(M:Rat)⟩ : QComplex)=QComplex.scaleRat (1/(M:Rat)) ⟨0,R.val⟩ := by
    simp only [QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  exact rationalWeightedSample_scale _ _ _

theorem common_inner_left_upper_average (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (squareFrameVerticalEdge f R M 1 1).val.Equiv
      (neg (commonSquareKernelAverage f ⟨.west,true⟩ R M).val) := by
  let density := fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point ⟨.west,true⟩ (1-squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.west,true⟩)))
  have hv : QComplex.scaleRat R.val (velocity ⟨.west,true⟩)=
      QComplex.scaleRat (-1) (⟨0,R.val⟩ : QComplex) := by
    simp only [velocity,rotation,orientation,Bool.false_eq_true,↓reduceIte,
      QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  have he (v : Nat) : (rectangleGridVertical f (squareFrameTile R 1 1) M 0 v).val.Equiv
      (scaleRat (-(1/(M:Rat))) (density v).val) := by
    have hs := common_inner_left_upper_sample f R M v hM
    have ht := weightedSample_signed_scale
      (f (QComplex.scaleRat R.val (point ⟨.west,true⟩ (1-squareMidpointParameter M v))))
      ⟨0,R.val⟩ (1/(M:Rat))
    rw [←hv] at ht
    exact equiv_trans (rectangleGridVertical f (squareFrameTile R 1 1) M 0 v).property
      (scaleRat_valid (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.west,true⟩ (1-squareMidpointParameter M v))))
        (rationalRectangleScalar ⟨0,R.val⟩)).property)
      (scaleRat_valid (density v).property) hs ht
  let weighted := fun v => (⟨scaleRat (-(1/(M:Rat))) (density v).val,
    scaleRat_valid (density v).property⟩ : Scalar)
  have hs := gridScalarSum_congr M _ weighted he
  have ht := gridScalarSum_scale (-(1/(M:Rat))) density M
  have hn := negativeScale_equiv_negScale (gridScalarSum M density) (1/(M:Rat))
  have hr := neg_equiv (commonReflectedSquareAverage_agreement f ⟨.west,true⟩ R M hM)
  exact equiv_trans (squareFrameVerticalEdge f R M 1 1).property
    (gridScalarSum M weighted).property
    (neg_valid (commonSquareKernelAverage f ⟨.west,true⟩ R M).property) hs
    (equiv_trans (gridScalarSum M weighted).property
      (scaleRat_valid (gridScalarSum M density).property)
      (neg_valid (commonSquareKernelAverage f ⟨.west,true⟩ R M).property) ht
      (equiv_trans (scaleRat_valid (gridScalarSum M density).property)
        (neg_valid (commonReflectedSquareAverage f ⟨.west,true⟩ R M).property)
        (neg_valid (commonSquareKernelAverage f ⟨.west,true⟩ R M).property) hn hr))

theorem common_inner_top_lower_sample (f : QComplex → Scalar) (R : QPos)
    (M v : Nat) (hM : 0<M) :
    (rectangleGridHorizontal f (squareFrameTile R 2 3) M v 0).val.Equiv
      (scaleRat (1/(M:Rat)) (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.north,false⟩ (squareMidpointParameter M v))))
        (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.north,false⟩)))).val) := by
  rw [←squareFrameTile_shared_horizontal_samples f R M 2 2 v hM]
  unfold rectangleGridHorizontal
  rw [squareFrame_inner_top_point R M 2 v hM,(squareFrameTile_grid_steps R M 2 2).1]
  have hp : cartesianSquarePoint ⟨.north,true⟩ R.val
      (2-((2:Nat):Rat)-((v:Rat)+1/2)/(M:Rat))=
      QComplex.scaleRat R.val (point ⟨.north,false⟩ (squareMidpointParameter M v)) := by
    rw [show ((2:Nat):Rat)=(2:Rat) by decide +kernel]
    simp only [cartesianSquarePoint,point,rotation,orientation,squareMidpointParameter,
      Bool.false_eq_true,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  rw [hp]
  have hw : (⟨R.val/(M:Rat),0⟩ : QComplex)=QComplex.scaleRat (1/(M:Rat)) ⟨R.val,0⟩ := by
    simp only [QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  have hv : QComplex.scaleRat R.val (velocity ⟨.north,false⟩)=⟨R.val,0⟩ := by
    simp only [velocity,rotation,orientation,Bool.false_eq_true,↓reduceIte,QComplex.mul,QComplex.scaleRat,
      Rat.mul_zero,Rat.mul_one,Rat.sub_self,Rat.add_zero,Rat.sub_eq_add_neg,Rat.neg_neg,Rat.zero_add,Rat.one_mul,Rat.zero_mul,Rat.neg_zero]
    all_goals simp only [QComplex.mk.injEq]
    all_goals constructor <;> grind only
  rw [hv]
  exact rationalWeightedSample_scale _ _ _

theorem common_inner_top_lower_average (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (squareFrameHorizontalEdge f R M 2 3).val.Equiv
      (commonSquareKernelAverage f ⟨.north,false⟩ R M).val := by
  let density := fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point ⟨.north,false⟩ (squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.north,false⟩)))
  have hs := gridScalarSum_congr M _
    (fun v => (⟨scaleRat (1/(M:Rat)) (density v).val,scaleRat_valid (density v).property⟩ : Scalar))
    (fun v => common_inner_top_lower_sample f R M v hM)
  exact equiv_trans (squareFrameHorizontalEdge f R M 2 3).property
    (gridScalarSum M (fun v => (⟨scaleRat (1/(M:Rat)) (density v).val,
      scaleRat_valid (density v).property⟩ : Scalar))).property
    (commonSquareKernelAverage f ⟨.north,false⟩ R M).property hs
    (gridScalarSum_scale (1/(M:Rat)) density M)

theorem common_inner_left_lower_sample (f : QComplex → Scalar) (R : QPos)
    (M v : Nat) (hM : 0<M) :
    (rectangleGridVertical f (squareFrameTile R 1 2) M 0 v).val.Equiv
      (scaleRat (1/(M:Rat)) (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.west,false⟩ (squareMidpointParameter M v))))
        (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.west,false⟩)))).val) := by
  unfold rectangleGridVertical
  rw [squareFrame_inner_left_point R M 2 v hM,(squareFrameTile_grid_steps R M 1 2).2]
  have hp : cartesianSquarePoint ⟨.west,true⟩ R.val
      (2-((2:Nat):Rat)-((v:Rat)+1/2)/(M:Rat))=
      QComplex.scaleRat R.val (point ⟨.west,false⟩ (squareMidpointParameter M v)) := by
    rw [show ((2:Nat):Rat)=(2:Rat) by decide +kernel]
    simp only [cartesianSquarePoint,point,rotation,orientation,squareMidpointParameter,
      Bool.false_eq_true,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  rw [hp]
  have hw : (⟨0,R.val/(M:Rat)⟩ : QComplex)=QComplex.scaleRat (1/(M:Rat)) ⟨0,R.val⟩ := by
    simp only [QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  have hv : QComplex.scaleRat R.val (velocity ⟨.west,false⟩)=⟨0,R.val⟩ := by
    simp only [velocity,rotation,orientation,Bool.false_eq_true,↓reduceIte,QComplex.mul,QComplex.scaleRat,
      Rat.mul_zero,Rat.mul_one,Rat.sub_self,Rat.add_zero,Rat.sub_eq_add_neg,Rat.neg_neg,Rat.zero_add,Rat.one_mul,Rat.zero_mul,Rat.neg_zero]
    all_goals simp only [QComplex.mk.injEq]
    all_goals constructor <;> grind only
  rw [hv]
  exact rationalWeightedSample_scale _ _ _

theorem common_inner_left_lower_average (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (squareFrameVerticalEdge f R M 1 2).val.Equiv
      (commonSquareKernelAverage f ⟨.west,false⟩ R M).val := by
  let density := fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point ⟨.west,false⟩ (squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.west,false⟩)))
  have hs := gridScalarSum_congr M _
    (fun v => (⟨scaleRat (1/(M:Rat)) (density v).val,scaleRat_valid (density v).property⟩ : Scalar))
    (fun v => common_inner_left_lower_sample f R M v hM)
  exact equiv_trans (squareFrameVerticalEdge f R M 1 2).property
    (gridScalarSum M (fun v => (⟨scaleRat (1/(M:Rat)) (density v).val,
      scaleRat_valid (density v).property⟩ : Scalar))).property
    (commonSquareKernelAverage f ⟨.west,false⟩ R M).property hs
    (gridScalarSum_scale (1/(M:Rat)) density M)

end ComputableAnalysis.RiemannHilbert.RectangularContour
