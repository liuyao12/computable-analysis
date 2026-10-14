import ComputableAnalysis.ModularForms.ActualSquareDensityAffineAgreement

/-! Exact finite contour comparison with the actual local affine model. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

def sampledSquareHalfEdge (f : Rat → Scalar) (edge : HalfEdge) (M : Nat) : Scalar :=
  let terms := gridScalarSum M (fun v => f
    (if edge.upper then squareMidpointParameter M v else 1-squareMidpointParameter M v))
  ⟨scaleRat ((M:Rat)⁻¹) terms.val,scaleRat_valid terms.property⟩

theorem gridScalarSum_sub_agreement (f g : Nat → Scalar) (M : Nat) :
    (gridScalarSub (gridScalarSum M f) (gridScalarSum M g)).val.Equiv
      (gridScalarSum M (fun v => gridScalarSub (f v) (g v))).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSub (gridScalarSum M f) (gridScalarSum M g)).property)
    (hright := (gridScalarSum M (fun v => gridScalarSub (f v) (g v))).property)
  change gridScalarValue (gridScalarSub (gridScalarSum M f) (gridScalarSum M g))=
    gridScalarValue (gridScalarSum M (fun v => gridScalarSub (f v) (g v)))
  simp only [gridScalarValue_sub,gridScalarSum_value,gridValueSum_sub]

theorem representedScale_sub_agreement (a b : Scalar) (r : Rat) :
    (sub (scaleRat r a.val) (scaleRat r b.val)).Equiv (scaleRat r (sub a.val b.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scaleRat_valid a.property) (scaleRat_valid b.property))
    (hright := scaleRat_valid (sub_valid a.property b.property))
  let A := gridScalarValue a
  let B := gridScalarValue b
  change ComplexRawQuotient.scaleRat r A-ComplexRawQuotient.scaleRat r B=
    ComplexRawQuotient.scaleRat r (A-B)
  change ComplexRawQuotient.scaleRat r A+ -(ComplexRawQuotient.scaleRat r B)=
    ComplexRawQuotient.scaleRat r (A+ -B)
  rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.neg_scaleRat,
    ComplexRawQuotient.neg_eq_scaleRat_neg_one,ComplexRawQuotient.scaleRat_scaleRat]
  congr 2
  grind only

theorem sampledSquareHalfEdge_sub_agreement (f g h : Rat → Scalar) (edge : HalfEdge)
    (M : Nat) (he : ∀ u, (sub (f u).val (g u).val).Equiv (h u).val) :
    (sub (sampledSquareHalfEdge f edge M).val (sampledSquareHalfEdge g edge M).val).Equiv
      (sampledSquareHalfEdge h edge M).val := by
  let p := fun v => if edge.upper then squareMidpointParameter M v else 1-squareMidpointParameter M v
  let F := gridScalarSum M (fun v => f (p v))
  let G := gridScalarSum M (fun v => g (p v))
  let H := gridScalarSum M (fun v => h (p v))
  let D := gridScalarSum M (fun v => gridScalarSub (f (p v)) (g (p v)))
  have hd := gridScalarSum_sub_agreement (fun v => f (p v)) (fun v => g (p v)) M
  have hh : D.val.Equiv H.val := gridScalarSum_congr M _ _ (fun v => he (p v))
  have ht : (sub F.val G.val).Equiv H.val :=
    equiv_trans (sub_valid F.property G.property) D.property H.property hd hh
  have hs := representedScale_congr (gridScalarSub F G) H ((M:Rat)⁻¹) ht
  exact equiv_trans
    (sub_valid (sampledSquareHalfEdge f edge M).property (sampledSquareHalfEdge g edge M).property)
    (scaleRat_valid (sub_valid F.property G.property)) (sampledSquareHalfEdge h edge M).property
    (representedScale_sub_agreement F G ((M:Rat)⁻¹)) hs

noncomputable def actualAffineSquareHalfEdge (c : Scalar) (edge : HalfEdge) (R : Rat) (M : Nat) : Scalar :=
  sampledSquareHalfEdge (affinePoleDensity (pairedEntireRiccatiMap.eval c trivial)
    (pairedEntireRiccatiMap_holomorphic.derivative c trivial) edge R) edge M

theorem actualSquareHalfEdge_affine_remainder (c : Scalar) (edge : HalfEdge) (R : Rat) (M : Nat) :
    (sub (sampledSquareHalfEdge (cartesianSquareKernelDensity c edge R) edge M).val
      (actualAffineSquareHalfEdge c edge R M).val).Equiv
      (squareDerivativeRemainderHalfEdgeSum c edge R M).val :=
  sampledSquareHalfEdge_sub_agreement _ _ _ edge M
    (fun u => actualSquareDensity_affine_remainder c edge R u)

theorem sampledActualSquareHalfEdge_original (c : Scalar) (edge : HalfEdge) (R : Rat) (M : Nat) :
    (sampledSquareHalfEdge (cartesianSquareKernelDensity c edge R) edge M).val.Equiv
      (pairedSquareHalfEdgeSum c edge R M) := by
  let f := fun v => cartesianSquareKernelDensity c edge R
    (if edge.upper then squareMidpointParameter M v else 1-squareMidpointParameter M v)
  have hb := gridScalarSum_block_agreement f 0 M
  simp only [Nat.zero_add] at hb
  have he : (ScalarSeries.block (fun v => (f v).val) 0 M)=
      ScalarSeries.block (fun v => pairedSquareDensity c edge
        (if edge.upper then squareMidpointParameter M v else 1-squareMidpointParameter M v) R) 0 M := by
    congr 1
    funext v
    exact cartesianSquareKernelDensity_agreement c edge R _
  rw [he] at hb
  exact representedScale_congr (gridScalarSum M f)
    ⟨_,ScalarSeries.block_valid _ (fun v => pairedSquareDensity_valid c edge _ R) 0 M⟩
    ((M:Rat)⁻¹) hb

noncomputable def actualAffineSquareEdgeList (c : Scalar) (R : Rat) (M : Nat) : List HalfEdge → Scalar
  | [] => ⟨zero,ofQComplex_valid _⟩
  | e::es => scalarSum (actualAffineSquareHalfEdge c e R M) (actualAffineSquareEdgeList c R M es)

theorem originalSquareHalfEdge_affine_remainder (c : Scalar) (edge : HalfEdge) (R : Rat) (M : Nat) :
    (sub (pairedSquareHalfEdgeSum c edge R M) (actualAffineSquareHalfEdge c edge R M).val).Equiv
      (squareDerivativeRemainderHalfEdgeSum c edge R M).val := by
  have hs := FunctionTheory.sub_congr
    (equiv_symm (sampledActualSquareHalfEdge_original c edge R M))
    (equiv_refl _ (actualAffineSquareHalfEdge c edge R M).property)
  exact equiv_trans
    (sub_valid (pairedSquareHalfEdgeSum_valid c edge R M) (actualAffineSquareHalfEdge c edge R M).property)
    (sub_valid (sampledSquareHalfEdge (cartesianSquareKernelDensity c edge R) edge M).property
      (actualAffineSquareHalfEdge c edge R M).property)
    (squareDerivativeRemainderHalfEdgeSum c edge R M).property hs
    (actualSquareHalfEdge_affine_remainder c edge R M)

theorem originalSquareEdgeList_affine_remainder (c : Scalar) (R : Rat) (M : Nat) (es : List HalfEdge) :
    (sub (pairedSquareEdgeListSum c R M es) (actualAffineSquareEdgeList c R M es).val).Equiv
      (squareDerivativeRemainderEdgeList c R M es).val := by
  induction es with
  | nil =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
      (hright := ofQComplex_valid _)
    change (0:ScalarAlgebra.Value)-0=0
    grind only
  | cons e es ih =>
    have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := sub_valid (pairedSquareHalfEdgeSum_valid c e R M) (actualAffineSquareHalfEdge c e R M).property)
      (hright := (squareDerivativeRemainderHalfEdgeSum c e R M).property)
      (originalSquareHalfEdge_affine_remainder c e R M)
    have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := sub_valid (pairedSquareEdgeListSum_valid c R M es) (actualAffineSquareEdgeList c R M es).property)
      (hright := (squareDerivativeRemainderEdgeList c R M es).property) ih
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedSquareEdgeListSum_valid c R M (e::es))
        (actualAffineSquareEdgeList c R M (e::es)).property)
      (hright := (squareDerivativeRemainderEdgeList c R M (e::es)).property)
    let A := ComplexRawQuotient.ofRaw (pairedSquareHalfEdgeSum c e R M) (pairedSquareHalfEdgeSum_valid c e R M)
    let B := ComplexRawQuotient.ofRaw (pairedSquareEdgeListSum c R M es) (pairedSquareEdgeListSum_valid c R M es)
    let C := gridScalarValue (actualAffineSquareHalfEdge c e R M)
    let D := gridScalarValue (actualAffineSquareEdgeList c R M es)
    let E := gridScalarValue (squareDerivativeRemainderHalfEdgeSum c e R M)
    let F := gridScalarValue (squareDerivativeRemainderEdgeList c R M es)
    change A-C=E at hh
    change B-D=F at ht
    change (A+B)-(C+D)=E+F
    grind only

theorem originalSquareContour_affine_error_bound (c : Scalar) (R eps : QPos)
    (M : Nat) (hM : 0<M)
    (hR : R.val≤((pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eps).val) :
    Small (sub (pairedSquareContourSum c R.val M)
      (actualAffineSquareEdgeList c R.val M square).val) (64*eps.val) := by
  exact Small.congr (squareDerivativeRemainderEdgeList c R.val M square).property
    (sub_valid (pairedSquareContourSum_valid c R.val M) (actualAffineSquareEdgeList c R.val M square).property)
    (equiv_symm (originalSquareEdgeList_affine_remainder c R.val M square))
    (squareDerivativeRemainderContour_bound c R eps M hM hR)

end ComputableAnalysis.ModularForms
