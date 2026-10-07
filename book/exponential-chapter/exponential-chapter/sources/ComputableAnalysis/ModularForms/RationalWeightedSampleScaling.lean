import ComputableAnalysis.ModularForms.SquareContourInnerGeometry

/-! Exact scaling laws for literal rational-weighted kernel samples. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem rationalRectangleScalar_scale (q : QComplex) (r : Rat) :
    (rationalRectangleScalar (QComplex.scaleRat r q)).val=
      scaleRat r (rationalRectangleScalar q).val := by
  simp only [rationalRectangleScalar,scaleRat,ofQComplex,QBox.scaleRat,QComplex.scaleRat]
  apply congrArg (fun f : Nat → QBox => ({compute := f} : ComplexRaw))
  funext n
  split <;> rfl

theorem rationalWeightedSample_scale (z : Scalar) (q : QComplex) (r : Rat) :
    (scalarProduct z (rationalRectangleScalar (QComplex.scaleRat r q))).val.Equiv
      (scaleRat r (scalarProduct z (rationalRectangleScalar q)).val) := by
  let w := rationalRectangleScalar q
  have hs : (rationalRectangleScalar (QComplex.scaleRat r q)).val=scaleRat r w.val :=
    rationalRectangleScalar_scale q r
  have ha := mul_comm_equiv z.val (scaleRat r w.val) z.property (scaleRat_valid w.property)
  have hb := scaleRat_mul_equiv r w.val z.val w.property z.property
  have hc : (scaleRat r (mul w.val z.val)).Equiv (scaleRat r (mul z.val w.val)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (mul_valid w.property z.property))
      (hright := scaleRat_valid (mul_valid z.property w.property))
    rw [ComplexRawQuotient.ofRaw_scaleRat,ComplexRawQuotient.ofRaw_scaleRat]
    congr 1
    exact ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := mul_valid w.property z.property) (hright := mul_valid z.property w.property)
      (mul_comm_equiv w.val z.val w.property z.property)
  change (mul z.val (rationalRectangleScalar (QComplex.scaleRat r q)).val).Equiv _
  rw [hs]
  exact equiv_trans (mul_valid z.property (scaleRat_valid w.property))
    (mul_valid (scaleRat_valid w.property) z.property)
    (scaleRat_valid (mul_valid z.property w.property)) ha
    (equiv_trans (mul_valid (scaleRat_valid w.property) z.property)
      (scaleRat_valid (mul_valid w.property z.property))
      (scaleRat_valid (mul_valid z.property w.property)) (equiv_symm hb) hc)

open PDE.CauchyContour

theorem squareFrame_inner_right_weighted_sample (c : Scalar) (R : QPos) (M k v : Nat) (hM : 0<M) :
    (rectangleGridVertical (rationalRiccatiKernelSample c) (squareFrameTile R 2 k) M M v).val.Equiv
      (scaleRat (1/(M:Rat)) (pairedSquareDensitySample c ⟨.east,true⟩ R.val
        ((k:Rat)-2+squareMidpointParameter M v)).val) := by
  unfold rectangleGridVertical
  rw [squareFrame_inner_right_point R M k v hM,(squareFrameTile_grid_steps R M 2 k).2]
  have hw : (⟨0,R.val/(M:Rat)⟩ : QComplex)=QComplex.scaleRat (1/(M:Rat)) ⟨0,R.val⟩ := by
    simp only [QComplex.scaleRat,QComplex.mk.injEq,Rat.div_def]
    constructor <;> grind only
  rw [hw]
  have hb := rationalWeightedSample_scale
    (rationalRiccatiKernelSample c (cartesianSquarePoint ⟨.east,true⟩ R.val
      ((k:Rat)-2+squareMidpointParameter M v))) ⟨0,R.val⟩ (1/(M:Rat))
  have hd : (cartesianSquareKernelDensity c ⟨.east,true⟩ R.val
      ((k:Rat)-2+squareMidpointParameter M v)).val=
    (scalarProduct (rationalRiccatiKernelSample c (cartesianSquarePoint ⟨.east,true⟩ R.val
      ((k:Rat)-2+squareMidpointParameter M v))) (rationalRectangleScalar ⟨0,R.val⟩)).val := by
    simp only [cartesianSquareKernelDensity,velocity,rotation,orientation,↓reduceIte,
      QComplex.mul,QComplex.scaleRat,Rat.mul_zero,Rat.mul_one,
      Rat.sub_self,Rat.add_zero]
  rw [←hd,cartesianSquareKernelDensity_agreement] at hb
  exact hb

end ComputableAnalysis.ModularForms

