import ComputableAnalysis.ModularForms.CartesianHalfEdgeSums

/-! The inner right edge is the sum of the original two east half-edge sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squareFrame_inner_right_tile_sum (c : Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (upper : Bool) :
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 (if upper then 2 else 1)).val.Equiv
      (cartesianHalfEdgeSum c .east R.val M upper).val := by
  let k := if upper then 2 else 1
  let f := fun v => pairedSquareDensitySample c ⟨.east,true⟩ R.val
    (if upper then squareMidpointParameter M v else squareMidpointParameter M v-1)
  let weighted := fun v => (⟨scaleRat ((M:Rat)⁻¹) (f v).val,scaleRat_valid (f v).property⟩ : Scalar)
  have hp (v : Nat) : (k:Rat)-2+squareMidpointParameter M v=
      (if upper then squareMidpointParameter M v else squareMidpointParameter M v-1) := by
    cases upper <;> dsimp [k] <;> grind only
  have he : ∀ v,
      (rectangleGridVertical (rationalRiccatiKernelSample c) (squareFrameTile R 3 k) M 0 v).val.Equiv
        (weighted v).val := by
    intro v
    rw [←squareFrameTile_shared_vertical_samples (rationalRiccatiKernelSample c) R M 2 k v hM]
    have hb := squareFrame_inner_right_weighted_sample c R M k v hM
    rw [hp] at hb
    simpa only [Rat.div_def,Rat.one_mul] using hb
  have ha := gridScalarSum_congr M _ weighted he
  have hb := gridScalarSum_scale ((M:Rat)⁻¹) f M
  exact equiv_trans
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 k).property
    (gridScalarSum M weighted).property
    (cartesianHalfEdgeSum c .east R.val M upper).property ha hb

theorem squareFrame_inner_right_tile_original_agreement (c : Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) (upper : Bool) :
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 (if upper then 2 else 1)).val.Equiv
      (pairedSquareHalfEdgeSum c ⟨.east,upper⟩ R.val M) :=
  equiv_trans
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 (if upper then 2 else 1)).property
    (cartesianHalfEdgeSum c .east R.val M upper).property
    (pairedSquareHalfEdgeSum_valid c ⟨.east,upper⟩ R.val M)
    (squareFrame_inner_right_tile_sum c R M hM upper)
    (cartesianHalfEdgeSum_agreement c .east R.val M hM upper)

theorem squareFrame_inner_right_full_edge_agreement (c : Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (gridScalarSum 2 (fun k => squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 (1+k))).val.Equiv
      (add (pairedSquareHalfEdgeSum c ⟨.east,false⟩ R.val M)
        (pairedSquareHalfEdgeSum c ⟨.east,true⟩ R.val M)) := by
  have hl := squareFrame_inner_right_tile_original_agreement c R M hM false
  have hu := squareFrame_inner_right_tile_original_agreement c R M hM true
  have hs := add_equiv hl hu
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum 2 (fun k => squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 (1+k))).property)
    (hright := add_valid (pairedSquareHalfEdgeSum_valid c ⟨.east,false⟩ R.val M)
      (pairedSquareHalfEdgeSum_valid c ⟨.east,true⟩ R.val M))
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 1).property
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 2).property)
    (hright := add_valid (pairedSquareHalfEdgeSum_valid c ⟨.east,false⟩ R.val M)
      (pairedSquareHalfEdgeSum_valid c ⟨.east,true⟩ R.val M)) hs
  change gridScalarValue (gridScalarSum 2 _)=_
  rw [gridScalarSum_value]
  simp only [gridValueSum,Nat.add_zero] 
  rw [←hv,ComplexRawQuotient.ofRaw_add]
  change (0+gridScalarValue (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 1))+
    gridScalarValue (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 2)=
      gridScalarValue (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 1)+
      gridScalarValue (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 3 2)
  grind only

end ComputableAnalysis.ModularForms
