import ComputableAnalysis.ModularForms.InnerSquareBottomEdgeSum

/-! Top and left tile sums with their actual orientation weights. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem representedScale_congr (a b : Scalar) (r : Rat) (h : a.val.Equiv b.val) :
    (scaleRat r a.val).Equiv (scaleRat r b.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid a.property) (hright := scaleRat_valid b.property)
  rw [ComplexRawQuotient.ofRaw_scaleRat,ComplexRawQuotient.ofRaw_scaleRat]
  congr 1
  exact ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := a.property) (hright := b.property) h

def negativeCartesianHalfEdgeSum (c : Scalar) (quarter : Quarter) (S : Rat) (M : Nat) (upper : Bool) : Scalar :=
  let terms := gridScalarSum M (fun v => pairedSquareDensitySample c ⟨quarter,true⟩ S
    (if upper then squareMidpointParameter M v else squareMidpointParameter M v-1))
  ⟨scaleRat (-1/(M:Rat)) terms.val,scaleRat_valid terms.property⟩

theorem squareFrame_inner_top_tile_sum (c : Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (upper : Bool) :
    (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (if upper then 1 else 2) 3).val.Equiv
      (negativeCartesianHalfEdgeSum c .north R.val M upper).val := by
  let k := if upper then 1 else 2
  let F := fun u => pairedSquareDensitySample c ⟨.north,true⟩ R.val
    (if upper then u else u-1)
  let f := fun v => F (1-squareMidpointParameter M v)
  let g := fun v => F (squareMidpointParameter M v)
  let weighted := fun v => (⟨scaleRat (-1/(M:Rat)) (f v).val,scaleRat_valid (f v).property⟩ : Scalar)
  have hp (v : Nat) : 2-(k:Rat)-squareMidpointParameter M v=
      (if upper then 1-squareMidpointParameter M v else (1-squareMidpointParameter M v)-1) := by
    cases upper <;> dsimp [k] <;> grind only
  have he : ∀ v,
      (rectangleGridHorizontal (rationalRiccatiKernelSample c) (squareFrameTile R k 3) M v 0).val.Equiv
        (weighted v).val := by
    intro v
    rw [←squareFrameTile_shared_horizontal_samples (rationalRiccatiKernelSample c) R M k 2 v hM]
    have hb := squareFrame_inner_top_weighted_sample c R M k v hM
    rw [hp] at hb
    exact hb
  have ha := gridScalarSum_congr M _ weighted he
  have hb := gridScalarSum_scale (-1/(M:Rat)) f M
  have hc := representedScale_congr (gridScalarSum M f) (gridScalarSum M g) (-1/(M:Rat))
    (gridScalarSum_reflected_parameters F M hM)
  exact equiv_trans (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M k 3).property
    (gridScalarSum M weighted).property
    (negativeCartesianHalfEdgeSum c .north R.val M upper).property ha
    (equiv_trans (gridScalarSum M weighted).property (scaleRat_valid (gridScalarSum M f).property)
      (negativeCartesianHalfEdgeSum c .north R.val M upper).property hb hc)

theorem squareFrame_inner_left_tile_sum (c : Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (upper : Bool) :
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 1 (if upper then 1 else 2)).val.Equiv
      (negativeCartesianHalfEdgeSum c .west R.val M upper).val := by
  let k := if upper then 1 else 2
  let F := fun u => pairedSquareDensitySample c ⟨.west,true⟩ R.val
    (if upper then u else u-1)
  let f := fun v => F (1-squareMidpointParameter M v)
  let g := fun v => F (squareMidpointParameter M v)
  let weighted := fun v => (⟨scaleRat (-1/(M:Rat)) (f v).val,scaleRat_valid (f v).property⟩ : Scalar)
  have hp (v : Nat) : 2-(k:Rat)-squareMidpointParameter M v=
      (if upper then 1-squareMidpointParameter M v else (1-squareMidpointParameter M v)-1) := by
    cases upper <;> dsimp [k] <;> grind only
  have he : ∀ v,
      (rectangleGridVertical (rationalRiccatiKernelSample c) (squareFrameTile R 1 k) M 0 v).val.Equiv
        (weighted v).val := by
    intro v
    have hb := squareFrame_inner_left_weighted_sample c R M k v hM
    rw [hp] at hb
    exact hb
  have ha := gridScalarSum_congr M _ weighted he
  have hb := gridScalarSum_scale (-1/(M:Rat)) f M
  have hc := representedScale_congr (gridScalarSum M f) (gridScalarSum M g) (-1/(M:Rat))
    (gridScalarSum_reflected_parameters F M hM)
  exact equiv_trans (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 1 k).property
    (gridScalarSum M weighted).property
    (negativeCartesianHalfEdgeSum c .west R.val M upper).property ha
    (equiv_trans (gridScalarSum M weighted).property (scaleRat_valid (gridScalarSum M f).property)
      (negativeCartesianHalfEdgeSum c .west R.val M upper).property hb hc)

theorem negativeCartesianHalfEdgeSum_agreement (c : Scalar) (quarter : Quarter)
    (S : Rat) (M : Nat) (hM : 0<M) (upper : Bool) :
    (negativeCartesianHalfEdgeSum c quarter S M upper).val.Equiv
      (neg (pairedSquareHalfEdgeSum c ⟨quarter,upper⟩ S M)) := by
  let terms := gridScalarSum M (fun v => pairedSquareDensitySample c ⟨quarter,true⟩ S
    (if upper then squareMidpointParameter M v else squareMidpointParameter M v-1))
  have hs := scaleRat_scaleRat_equiv (-1) ((M:Rat)⁻¹) terms.val terms.property
  have hn := neg_equiv_scaleRat_neg_one (cartesianHalfEdgeSum c quarter S M upper).val
    (cartesianHalfEdgeSum c quarter S M upper).property
  have hb := neg_equiv (cartesianHalfEdgeSum_agreement c quarter S M hM upper)
  have he : (-1/(M:Rat))=(-1)*((M:Rat)⁻¹) := by rw [Rat.div_def]
  change (scaleRat (-1/(M:Rat)) terms.val).Equiv _
  rw [he]
  exact equiv_trans (scaleRat_valid terms.property)
    (scaleRat_valid (cartesianHalfEdgeSum c quarter S M upper).property)
    (neg_valid (pairedSquareHalfEdgeSum_valid c ⟨quarter,upper⟩ S M))
    (equiv_symm hs)
    (equiv_trans (scaleRat_valid (cartesianHalfEdgeSum c quarter S M upper).property)
      (neg_valid (cartesianHalfEdgeSum c quarter S M upper).property)
      (neg_valid (pairedSquareHalfEdgeSum_valid c ⟨quarter,upper⟩ S M)) (equiv_symm hn) hb)

end ComputableAnalysis.ModularForms

