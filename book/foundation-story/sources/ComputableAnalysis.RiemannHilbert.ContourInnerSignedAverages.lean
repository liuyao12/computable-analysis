import ComputableAnalysis.RiemannHilbert.ContourInnerReflectedEdges

/-! Signed velocity and inner-square average comparisons. Generic finite proofs adapted from the corresponding
`ModularForms` files; those original files are preserved. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

theorem weightedSample_signed_scale (z : Scalar) (q : QComplex) (r : Rat) :
    (scaleRat r (scalarProduct z (rationalRectangleScalar q)).val).Equiv
      (scaleRat (-r) (scalarProduct z (rationalRectangleScalar (QComplex.scaleRat (-1) q))).val) := by
  have hs := scaleRat_equiv (r := -r) (rationalWeightedSample_scale z q (-1))
  have ht := scaleRat_scaleRat_equiv (-r) (-1)
    (scalarProduct z (rationalRectangleScalar q)).val (scalarProduct z (rationalRectangleScalar q)).property
  have he : (-r)*(-1)=r := by grind only
  rw [he] at ht
  exact equiv_symm (equiv_trans
    (scaleRat_valid (scalarProduct z (rationalRectangleScalar (QComplex.scaleRat (-1) q))).property)
    (scaleRat_valid (scaleRat_valid (scalarProduct z (rationalRectangleScalar q)).property))
    (scaleRat_valid (scalarProduct z (rationalRectangleScalar q)).property) hs ht)

theorem negativeScale_equiv_negScale (z : Scalar) (r : Rat) :
    (scaleRat (-r) z.val).Equiv (neg (scaleRat r z.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid z.property) (hright := neg_valid (scaleRat_valid z.property))
  rw [ComplexRawQuotient.ofRaw_neg,ComplexRawQuotient.ofRaw_scaleRat,
    ComplexRawQuotient.ofRaw_scaleRat,ComplexRawQuotient.neg_scaleRat]
  all_goals first | exact z.property | exact scaleRat_valid z.property

theorem common_inner_right_lower_average (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (squareFrameVerticalEdge f R M 3 1).val.Equiv
      (neg (commonSquareKernelAverage f ⟨.east,false⟩ R M).val) := by
  let density := fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point ⟨.east,false⟩ (1-squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.east,false⟩)))
  have hv : QComplex.scaleRat R.val (velocity ⟨.east,false⟩)=
      QComplex.scaleRat (-1) (⟨0,R.val⟩ : QComplex) := by
    simp only [velocity,rotation,orientation,Bool.false_eq_true,↓reduceIte,
      QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  have he (v : Nat) : (rectangleGridVertical f (squareFrameTile R 3 1) M 0 v).val.Equiv
      (scaleRat (-(1/(M:Rat))) (density v).val) := by
    have hs := common_inner_right_lower_sample f R M v hM
    have ht := weightedSample_signed_scale
      (f (QComplex.scaleRat R.val (point ⟨.east,false⟩ (1-squareMidpointParameter M v))))
      ⟨0,R.val⟩ (1/(M:Rat))
    rw [←hv] at ht
    exact equiv_trans (rectangleGridVertical f (squareFrameTile R 3 1) M 0 v).property
      (scaleRat_valid (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.east,false⟩ (1-squareMidpointParameter M v))))
        (rationalRectangleScalar ⟨0,R.val⟩)).property)
      (scaleRat_valid (density v).property) hs ht
  let weighted := fun v => (⟨scaleRat (-(1/(M:Rat))) (density v).val,
    scaleRat_valid (density v).property⟩ : Scalar)
  have hs := gridScalarSum_congr M _ weighted he
  have ht := gridScalarSum_scale (-(1/(M:Rat))) density M
  have hn := negativeScale_equiv_negScale (gridScalarSum M density) (1/(M:Rat))
  have hr := neg_equiv (commonReflectedSquareAverage_agreement f ⟨.east,false⟩ R M hM)
  exact equiv_trans (squareFrameVerticalEdge f R M 3 1).property
    (gridScalarSum M weighted).property
    (neg_valid (commonSquareKernelAverage f ⟨.east,false⟩ R M).property) hs
    (equiv_trans (gridScalarSum M weighted).property
      (scaleRat_valid (gridScalarSum M density).property)
      (neg_valid (commonSquareKernelAverage f ⟨.east,false⟩ R M).property) ht
      (equiv_trans (scaleRat_valid (gridScalarSum M density).property)
        (neg_valid (commonReflectedSquareAverage f ⟨.east,false⟩ R M).property)
        (neg_valid (commonSquareKernelAverage f ⟨.east,false⟩ R M).property) hn hr))

theorem common_inner_bottom_lower_average (f : QComplex → Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (squareFrameHorizontalEdge f R M 1 1).val.Equiv
      (neg (commonSquareKernelAverage f ⟨.south,false⟩ R M).val) := by
  let density := fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point ⟨.south,false⟩ (1-squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity ⟨.south,false⟩)))
  have hv : QComplex.scaleRat R.val (velocity ⟨.south,false⟩)=
      QComplex.scaleRat (-1) (⟨R.val,0⟩ : QComplex) := by
    simp only [velocity,rotation,orientation,Bool.false_eq_true,↓reduceIte,
      QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  have he (v : Nat) : (rectangleGridHorizontal f (squareFrameTile R 1 1) M v 0).val.Equiv
      (scaleRat (-(1/(M:Rat))) (density v).val) := by
    have hs := common_inner_bottom_lower_sample f R M v hM
    have ht := weightedSample_signed_scale
      (f (QComplex.scaleRat R.val (point ⟨.south,false⟩ (1-squareMidpointParameter M v))))
      ⟨R.val,0⟩ (1/(M:Rat))
    rw [←hv] at ht
    exact equiv_trans (rectangleGridHorizontal f (squareFrameTile R 1 1) M v 0).property
      (scaleRat_valid (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.south,false⟩ (1-squareMidpointParameter M v))))
        (rationalRectangleScalar ⟨R.val,0⟩)).property)
      (scaleRat_valid (density v).property) hs ht
  let weighted := fun v => (⟨scaleRat (-(1/(M:Rat))) (density v).val,
    scaleRat_valid (density v).property⟩ : Scalar)
  have hs := gridScalarSum_congr M _ weighted he
  have ht := gridScalarSum_scale (-(1/(M:Rat))) density M
  have hn := negativeScale_equiv_negScale (gridScalarSum M density) (1/(M:Rat))
  have hr := neg_equiv (commonReflectedSquareAverage_agreement f ⟨.south,false⟩ R M hM)
  exact equiv_trans (squareFrameHorizontalEdge f R M 1 1).property
    (gridScalarSum M weighted).property
    (neg_valid (commonSquareKernelAverage f ⟨.south,false⟩ R M).property) hs
    (equiv_trans (gridScalarSum M weighted).property
      (scaleRat_valid (gridScalarSum M density).property)
      (neg_valid (commonSquareKernelAverage f ⟨.south,false⟩ R M).property) ht
      (equiv_trans (scaleRat_valid (gridScalarSum M density).property)
        (neg_valid (commonReflectedSquareAverage f ⟨.south,false⟩ R M).property)
        (neg_valid (commonSquareKernelAverage f ⟨.south,false⟩ R M).property) hn hr))

end ComputableAnalysis.RiemannHilbert.RectangularContour
