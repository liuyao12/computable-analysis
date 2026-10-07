import ComputableAnalysis.ModularForms.ActualSquareContourAffineAgreement

/-! Finite affine contour residues, including the lower-edge reindexing. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem sampledSquareHalfEdge_midpoint (f : Rat → Scalar) (edge : HalfEdge)
    (M : Nat) (hM : 0<M) :
    (sampledSquareHalfEdge f edge M).val.Equiv
      (weightedMidpointSum f M ((M:Rat)⁻¹)).val := by
  cases he : edge.upper with
  | true =>
    simp only [sampledSquareHalfEdge,he,↓reduceIte]
    exact equiv_refl _ (weightedMidpointSum f M ((M:Rat)⁻¹)).property
  | false =>
    simp only [sampledSquareHalfEdge,he,Bool.false_eq_true,↓reduceIte]
    have h := gridScalarSum_reflected_parameters f M hM
    exact representedScale_congr
      (gridScalarSum M (fun v => f (1-squareMidpointParameter M v)))
      (gridScalarSum M (fun v => f (squareMidpointParameter M v))) ((M:Rat)⁻¹) h

theorem weightedMidpointSum_add (f g : Rat → Scalar) (M : Nat) (r : Rat) :
    (scalarSum (weightedMidpointSum f M r) (weightedMidpointSum g M r)).val.Equiv
      (weightedMidpointSum (fun u => scalarSum (f u) (g u)) M r).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scalarSum (weightedMidpointSum f M r) (weightedMidpointSum g M r)).property)
    (hright := (weightedMidpointSum (fun u => scalarSum (f u) (g u)) M r).property)
  change ComplexRawQuotient.scaleRat r (gridScalarValue (gridScalarSum M (fun v => f (squareMidpointParameter M v))))+
    ComplexRawQuotient.scaleRat r (gridScalarValue (gridScalarSum M (fun v => g (squareMidpointParameter M v))))=
    ComplexRawQuotient.scaleRat r (gridScalarValue
      (gridScalarSum M (fun v => scalarSum (f (squareMidpointParameter M v)) (g (squareMidpointParameter M v)))))
  simp only [gridScalarSum_value,gridScalarValue_add,gridValueSum_add,ComplexRawQuotient.scaleRat_add]

theorem actualAffineSquareEdgeList_midpoint (c : Scalar) (R : Rat) (M : Nat)
    (hM : 0<M) (es : List HalfEdge) :
    (actualAffineSquareEdgeList c R M es).val.Equiv
      (weightedMidpointSum (fun u => affinePoleEdgeList (pairedEntireRiccatiMap.eval c trivial)
        (pairedEntireRiccatiMap_holomorphic.derivative c trivial) R u es) M ((M:Rat)⁻¹)).val := by
  induction es with
  | nil =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (actualAffineSquareEdgeList c R M []).property)
      (hright := (weightedMidpointSum (fun u => affinePoleEdgeList (pairedEntireRiccatiMap.eval c trivial)
        (pairedEntireRiccatiMap_holomorphic.derivative c trivial) R u []) M ((M:Rat)⁻¹)).property)
    change (0:ScalarAlgebra.Value)=ComplexRawQuotient.scaleRat ((M:Rat)⁻¹)
      (gridScalarValue (gridScalarSum M (fun _ => ⟨zero,ofQComplex_valid _⟩)))
    rw [gridScalarSum_value]
    change (0:ScalarAlgebra.Value)=ComplexRawQuotient.scaleRat ((M:Rat)⁻¹) (gridValueSum M (fun _ => 0))
    rw [gridValueSum_zero]
    exact (ComplexRawQuotient.scaleRat_zero ((M:Rat)⁻¹)).symm
  | cons e es ih =>
    let f := affinePoleDensity (pairedEntireRiccatiMap.eval c trivial)
      (pairedEntireRiccatiMap_holomorphic.derivative c trivial) e R
    let g := fun u => affinePoleEdgeList (pairedEntireRiccatiMap.eval c trivial)
      (pairedEntireRiccatiMap_holomorphic.derivative c trivial) R u es
    have hh := sampledSquareHalfEdge_midpoint f e M hM
    have ha := add_equiv hh ih
    exact equiv_trans (actualAffineSquareEdgeList c R M (e::es)).property
      (scalarSum (weightedMidpointSum f M ((M:Rat)⁻¹)) (weightedMidpointSum g M ((M:Rat)⁻¹))).property
      (weightedMidpointSum (fun u => scalarSum (f u) (g u)) M ((M:Rat)⁻¹)).property ha
      (weightedMidpointSum_add f g M ((M:Rat)⁻¹))

def squareResidueMidpointSum (M : Nat) : Scalar :=
  weightedMidpointSum (fun u => rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩)
    M ((M:Rat)⁻¹)

theorem gridScalarSum_mul_left (d : Scalar) (f : Nat → Scalar) (M : Nat) :
    (gridScalarSum M (fun v => scalarProduct d (f v))).val.Equiv
      (scalarProduct d (gridScalarSum M f)).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum M (fun v => scalarProduct d (f v))).property)
    (hright := (scalarProduct d (gridScalarSum M f)).property)
  change gridScalarValue (gridScalarSum M (fun v => scalarProduct d (f v)))=
    gridScalarValue d*gridScalarValue (gridScalarSum M f)
  simp only [gridScalarSum_value]
  let D := gridScalarValue d
  let F := fun v => gridScalarValue (f v)
  change gridValueSum M (fun v => D*F v)=D*gridValueSum M F
  induction M with
  | zero => simp only [gridValueSum]; grind only
  | succ M ih => simp only [gridValueSum,ih]; grind only

theorem weightedMidpointSum_mul_left (d : Scalar) (f : Rat → Scalar) (M : Nat) (r : Rat) :
    (weightedMidpointSum (fun u => scalarProduct d (f u)) M r).val.Equiv
      (scalarProduct d (weightedMidpointSum f M r)).val := by
  have hs := gridScalarSum_mul_left d (fun v => f (squareMidpointParameter M v)) M
  have hh := representedScale_congr
    (gridScalarSum M (fun v => scalarProduct d (f (squareMidpointParameter M v))))
    (scalarProduct d (gridScalarSum M (fun v => f (squareMidpointParameter M v)))) r hs
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (weightedMidpointSum (fun u => scalarProduct d (f u)) M r).property)
    (hright := (scalarProduct d (weightedMidpointSum f M r)).property)
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (weightedMidpointSum (fun u => scalarProduct d (f u)) M r).property)
    (hright := scaleRat_valid (scalarProduct d (gridScalarSum M (fun v => f (squareMidpointParameter M v)))).property) hh
  rw [hv]
  exact (ComplexRawQuotient.mul_scaleRat r (gridScalarValue d)
    (gridScalarValue (gridScalarSum M (fun v => f (squareMidpointParameter M v))))).symm

theorem actualAffineSquareContour_finite_residue (c : Scalar) (R : Rat) (hR : 0<R)
    (M : Nat) (hM : 0<M) :
    (actualAffineSquareEdgeList c R M square).val.Equiv
      (scalarProduct (pairedEntireRiccatiMap_holomorphic.derivative c trivial)
        (squareResidueMidpointSum M)).val := by
  let d := pairedEntireRiccatiMap_holomorphic.derivative c trivial
  let f := fun u => affinePoleEdgeList (pairedEntireRiccatiMap.eval c trivial) d R u square
  let k := fun u => rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel u⟩
  have hg := gridScalarSum_congr M
    (fun v => f (squareMidpointParameter M v))
    (fun v => scalarProduct d (k (squareMidpointParameter M v)))
    (fun v => representedSquare_affine_residue_density (pairedEntireRiccatiMap.eval c trivial) d R _ hR)
  have hs := representedScale_congr
    (gridScalarSum M (fun v => f (squareMidpointParameter M v)))
    (gridScalarSum M (fun v => scalarProduct d (k (squareMidpointParameter M v)))) ((M:Rat)⁻¹) hg
  exact equiv_trans (actualAffineSquareEdgeList c R M square).property
    (weightedMidpointSum f M ((M:Rat)⁻¹)).property
    (scalarProduct d (squareResidueMidpointSum M)).property
    (actualAffineSquareEdgeList_midpoint c R M hM square)
    (equiv_trans (weightedMidpointSum f M ((M:Rat)⁻¹)).property
      (weightedMidpointSum (fun u => scalarProduct d (k u)) M ((M:Rat)⁻¹)).property
      (scalarProduct d (squareResidueMidpointSum M)).property hs
      (weightedMidpointSum_mul_left d k M ((M:Rat)⁻¹)))

theorem originalSquareContour_derivative_residue_error (c : Scalar) (R eps : QPos)
    (M : Nat) (hM : 0<M)
    (hR : R.val≤((pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eps).val) :
    Small (sub (pairedSquareContourSum c R.val M)
      (scalarProduct (pairedEntireRiccatiMap_holomorphic.derivative c trivial)
        (squareResidueMidpointSum M)).val) (64*eps.val) := by
  have he := actualAffineSquareContour_finite_residue c R.val R.property M hM
  exact Small.congr
    (sub_valid (pairedSquareContourSum_valid c R.val M)
      (actualAffineSquareEdgeList c R.val M square).property)
    (sub_valid (pairedSquareContourSum_valid c R.val M)
      (scalarProduct (pairedEntireRiccatiMap_holomorphic.derivative c trivial)
        (squareResidueMidpointSum M)).property)
    (FunctionTheory.sub_congr (equiv_refl _ (pairedSquareContourSum_valid c R.val M)) he)
    (originalSquareContour_affine_error_bound c R eps M hM hR)

end ComputableAnalysis.ModularForms
