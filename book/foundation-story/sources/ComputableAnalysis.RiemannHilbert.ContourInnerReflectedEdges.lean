import ComputableAnalysis.RiemannHilbert.ContourInnerForwardEdges

/-! Reflected inner-square half-edge comparisons. Generic finite proofs adapted from the corresponding
`ModularForms` files; those original files are preserved. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

def commonReflectedSquareAverage (f : QComplex → Scalar) (edge : HalfEdge)
    (R : QPos) (M : Nat) : Scalar :=
  let s := gridScalarSum M (fun v => scalarProduct
    (f (QComplex.scaleRat R.val (point edge (1-squareMidpointParameter M v))))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity edge))))
  ⟨scaleRat (1/(M:Rat)) s.val,scaleRat_valid s.property⟩

theorem commonReflectedSquareAverage_agreement (f : QComplex → Scalar) (edge : HalfEdge)
    (R : QPos) (M : Nat) (hM : 0<M) :
    (commonReflectedSquareAverage f edge R M).val.Equiv
      (commonSquareKernelAverage f edge R M).val := by
  apply scaleRat_equiv
  exact gridScalarSum_reflected_parameters (fun u => scalarProduct
    (f (QComplex.scaleRat R.val (point edge u)))
    (rationalRectangleScalar (QComplex.scaleRat R.val (velocity edge)))) M hM

theorem common_inner_right_lower_sample (f : QComplex → Scalar) (R : QPos)
    (M v : Nat) (hM : 0<M) :
    (rectangleGridVertical f (squareFrameTile R 3 1) M 0 v).val.Equiv
      (scaleRat (1/(M:Rat)) (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.east,false⟩ (1-squareMidpointParameter M v))))
        (rationalRectangleScalar ⟨0,R.val⟩)).val) := by
  rw [←squareFrameTile_shared_vertical_samples f R M 2 1 v hM]
  unfold rectangleGridVertical
  rw [squareFrame_inner_right_point R M 1 v hM,(squareFrameTile_grid_steps R M 2 1).2]
  have hp : cartesianSquarePoint ⟨.east,true⟩ R.val
      (((1:Nat):Rat)-2+((v:Rat)+1/2)/(M:Rat))=
      QComplex.scaleRat R.val (point ⟨.east,false⟩ (1-squareMidpointParameter M v)) := by
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

theorem common_inner_bottom_lower_sample (f : QComplex → Scalar) (R : QPos)
    (M v : Nat) (hM : 0<M) :
    (rectangleGridHorizontal f (squareFrameTile R 1 1) M v 0).val.Equiv
      (scaleRat (1/(M:Rat)) (scalarProduct
        (f (QComplex.scaleRat R.val (point ⟨.south,false⟩ (1-squareMidpointParameter M v))))
        (rationalRectangleScalar ⟨R.val,0⟩)).val) := by
  unfold rectangleGridHorizontal
  rw [squareFrame_inner_bottom_point R M 1 v hM,(squareFrameTile_grid_steps R M 1 1).1]
  have hp : cartesianSquarePoint ⟨.south,true⟩ R.val
      (((1:Nat):Rat)-2+((v:Rat)+1/2)/(M:Rat))=
      QComplex.scaleRat R.val (point ⟨.south,false⟩ (1-squareMidpointParameter M v)) := by
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

end ComputableAnalysis.RiemannHilbert.RectangularContour
