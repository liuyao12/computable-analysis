import ComputableAnalysis.ModularForms.RationalWeightedSampleScaling

/-! Exact weights for every Cartesian side of the two frame contours. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squareKernel_upper_weighted_sample (c : Scalar) (quarter : Quarter) (S u r : Rat) :
    (scalarProduct (rationalRiccatiKernelSample c (cartesianSquarePoint ⟨quarter,true⟩ S u))
      (rationalRectangleScalar (QComplex.scaleRat r (QComplex.scaleRat S (velocity ⟨quarter,true⟩))))).val.Equiv
      (scaleRat r (pairedSquareDensitySample c ⟨quarter,true⟩ S u).val) := by
  have hb := rationalWeightedSample_scale
    (rationalRiccatiKernelSample c (cartesianSquarePoint ⟨quarter,true⟩ S u))
    (QComplex.scaleRat S (velocity ⟨quarter,true⟩)) r
  have hd := cartesianSquareKernelDensity_agreement c ⟨quarter,true⟩ S u
  simp only [cartesianSquareKernelDensity,↓reduceIte] at hd
  rw [hd] at hb
  exact hb

theorem squareFrame_inner_top_weighted_sample (c : Scalar) (R : QPos) (M j v : Nat) (hM : 0<M) :
    (rectangleGridHorizontal (rationalRiccatiKernelSample c) (squareFrameTile R j 2) M v M).val.Equiv
      (scaleRat (-1/(M:Rat)) (pairedSquareDensitySample c ⟨.north,true⟩ R.val (2-(j:Rat)-squareMidpointParameter M v)).val) := by
  unfold rectangleGridHorizontal
  rw [squareFrame_inner_top_point R M j v hM,(squareFrameTile_grid_steps R M j 2).1]
  have hw : (⟨R.val/(M:Rat),0⟩ : QComplex)=
      QComplex.scaleRat (-1/(M:Rat)) (QComplex.scaleRat R.val (velocity ⟨.north,true⟩)) := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  exact squareKernel_upper_weighted_sample c .north R.val (2-(j:Rat)-squareMidpointParameter M v) (-1/(M:Rat))

theorem squareFrame_inner_left_weighted_sample (c : Scalar) (R : QPos) (M k v : Nat) (hM : 0<M) :
    (rectangleGridVertical (rationalRiccatiKernelSample c) (squareFrameTile R 1 k) M 0 v).val.Equiv
      (scaleRat (-1/(M:Rat)) (pairedSquareDensitySample c ⟨.west,true⟩ R.val (2-(k:Rat)-squareMidpointParameter M v)).val) := by
  unfold rectangleGridVertical
  rw [squareFrame_inner_left_point R M k v hM,(squareFrameTile_grid_steps R M 1 k).2]
  have hw : (⟨0,R.val/(M:Rat)⟩ : QComplex)=
      QComplex.scaleRat (-1/(M:Rat)) (QComplex.scaleRat R.val (velocity ⟨.west,true⟩)) := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  exact squareKernel_upper_weighted_sample c .west R.val (2-(k:Rat)-squareMidpointParameter M v) (-1/(M:Rat))

theorem squareFrame_inner_bottom_weighted_sample (c : Scalar) (R : QPos) (M j v : Nat) (hM : 0<M) :
    (rectangleGridHorizontal (rationalRiccatiKernelSample c) (squareFrameTile R j 1) M v 0).val.Equiv
      (scaleRat (1/(M:Rat)) (pairedSquareDensitySample c ⟨.south,true⟩ R.val ((j:Rat)-2+squareMidpointParameter M v)).val) := by
  unfold rectangleGridHorizontal
  rw [squareFrame_inner_bottom_point R M j v hM,(squareFrameTile_grid_steps R M j 1).1]
  have hw : (⟨R.val/(M:Rat),0⟩ : QComplex)=
      QComplex.scaleRat (1/(M:Rat)) (QComplex.scaleRat R.val (velocity ⟨.south,true⟩)) := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  exact squareKernel_upper_weighted_sample c .south R.val ((j:Rat)-2+squareMidpointParameter M v) (1/(M:Rat))

theorem squareFrame_outer_right_weighted_sample (c : Scalar) (R : QPos) (M k v : Nat) (hM : 0<M) :
    (rectangleGridVertical (rationalRiccatiKernelSample c) (squareFrameTile R 3 k) M M v).val.Equiv
      (scaleRat (1/(2*(M:Rat))) (pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val) (((k:Rat)-2+squareMidpointParameter M v)/2)).val) := by
  unfold rectangleGridVertical
  rw [squareFrame_outer_right_point R M k v hM,(squareFrameTile_grid_steps R M 3 k).2]
  have hw : (⟨0,R.val/(M:Rat)⟩ : QComplex)=
      QComplex.scaleRat (1/(2*(M:Rat))) (QComplex.scaleRat (2*R.val) (velocity ⟨.east,true⟩)) := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def,Rat.inv_mul_rev]
    constructor <;> grind only
  rw [hw]
  exact squareKernel_upper_weighted_sample c .east (2*R.val) (((k:Rat)-2+squareMidpointParameter M v)/2) (1/(2*(M:Rat)))

theorem squareFrame_outer_top_weighted_sample (c : Scalar) (R : QPos) (M j v : Nat) (hM : 0<M) :
    (rectangleGridHorizontal (rationalRiccatiKernelSample c) (squareFrameTile R j 3) M v M).val.Equiv
      (scaleRat (-1/(2*(M:Rat))) (pairedSquareDensitySample c ⟨.north,true⟩ (2*R.val) ((2-(j:Rat)-squareMidpointParameter M v)/2)).val) := by
  unfold rectangleGridHorizontal
  rw [squareFrame_outer_top_point R M j v hM,(squareFrameTile_grid_steps R M j 3).1]
  have hw : (⟨R.val/(M:Rat),0⟩ : QComplex)=
      QComplex.scaleRat (-1/(2*(M:Rat))) (QComplex.scaleRat (2*R.val) (velocity ⟨.north,true⟩)) := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def,Rat.inv_mul_rev]
    constructor <;> grind only
  rw [hw]
  exact squareKernel_upper_weighted_sample c .north (2*R.val) ((2-(j:Rat)-squareMidpointParameter M v)/2) (-1/(2*(M:Rat)))

theorem squareFrame_outer_left_weighted_sample (c : Scalar) (R : QPos) (M k v : Nat) (hM : 0<M) :
    (rectangleGridVertical (rationalRiccatiKernelSample c) (squareFrameTile R 0 k) M 0 v).val.Equiv
      (scaleRat (-1/(2*(M:Rat))) (pairedSquareDensitySample c ⟨.west,true⟩ (2*R.val) ((2-(k:Rat)-squareMidpointParameter M v)/2)).val) := by
  unfold rectangleGridVertical
  rw [squareFrame_outer_left_point R M k v hM,(squareFrameTile_grid_steps R M 0 k).2]
  have hw : (⟨0,R.val/(M:Rat)⟩ : QComplex)=
      QComplex.scaleRat (-1/(2*(M:Rat))) (QComplex.scaleRat (2*R.val) (velocity ⟨.west,true⟩)) := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def,Rat.inv_mul_rev]
    constructor <;> grind only
  rw [hw]
  exact squareKernel_upper_weighted_sample c .west (2*R.val) ((2-(k:Rat)-squareMidpointParameter M v)/2) (-1/(2*(M:Rat)))

theorem squareFrame_outer_bottom_weighted_sample (c : Scalar) (R : QPos) (M j v : Nat) (hM : 0<M) :
    (rectangleGridHorizontal (rationalRiccatiKernelSample c) (squareFrameTile R j 0) M v 0).val.Equiv
      (scaleRat (1/(2*(M:Rat))) (pairedSquareDensitySample c ⟨.south,true⟩ (2*R.val) (((j:Rat)-2+squareMidpointParameter M v)/2)).val) := by
  unfold rectangleGridHorizontal
  rw [squareFrame_outer_bottom_point R M j v hM,(squareFrameTile_grid_steps R M j 0).1]
  have hw : (⟨R.val/(M:Rat),0⟩ : QComplex)=
      QComplex.scaleRat (1/(2*(M:Rat))) (QComplex.scaleRat (2*R.val) (velocity ⟨.south,true⟩)) := by
    simp only [velocity,rotation,orientation,↓reduceIte,QComplex.mul,QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def,Rat.inv_mul_rev]
    constructor <;> grind only
  rw [hw]
  exact squareKernel_upper_weighted_sample c .south (2*R.val) (((j:Rat)-2+squareMidpointParameter M v)/2) (1/(2*(M:Rat)))

theorem gridValueSum_scale (r : Rat) (f : Nat → ScalarAlgebra.Value) (n : Nat) :
    gridValueSum n (fun j => ComplexRawQuotient.scaleRat r (f j))=
      ComplexRawQuotient.scaleRat r (gridValueSum n f) := by
  induction n with
  | zero => exact (ComplexRawQuotient.scaleRat_zero r).symm
  | succ n ih =>
    simp only [gridValueSum,ih,ComplexRawQuotient.scaleRat_add]

theorem gridScalarSum_scale (r : Rat) (f : Nat → Scalar) (n : Nat) :
    (gridScalarSum n (fun j => ⟨scaleRat r (f j).val,scaleRat_valid (f j).property⟩)).val.Equiv
      (scaleRat r (gridScalarSum n f).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum n (fun j => ⟨scaleRat r (f j).val,scaleRat_valid (f j).property⟩)).property)
    (hright := scaleRat_valid (gridScalarSum n f).property)
  change gridScalarValue (gridScalarSum n (fun j => ⟨scaleRat r (f j).val,scaleRat_valid (f j).property⟩))=
    ComplexRawQuotient.ofRaw (scaleRat r (gridScalarSum n f).val) _
  rw [gridScalarSum_value,ComplexRawQuotient.ofRaw_scaleRat]
  change gridValueSum n (fun j => ComplexRawQuotient.ofRaw (scaleRat r (f j).val) _)=
    ComplexRawQuotient.scaleRat r (gridScalarValue (gridScalarSum n f))
  simp only [ComplexRawQuotient.ofRaw_scaleRat,gridScalarSum_value]
  exact gridValueSum_scale r (fun j => gridScalarValue (f j)) n

end ComputableAnalysis.ModularForms

