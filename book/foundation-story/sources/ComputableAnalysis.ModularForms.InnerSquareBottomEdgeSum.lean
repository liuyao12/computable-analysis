import ComputableAnalysis.ModularForms.InnerSquareRightEdgeSum

/-! The inner bottom edge agrees with the original two south half-edge sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squareFrame_inner_bottom_tile_sum (c : Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (upper : Bool) :
    (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (if upper then 2 else 1) 1).val.Equiv
      (cartesianHalfEdgeSum c .south R.val M upper).val := by
  let k := if upper then 2 else 1
  let f := fun v => pairedSquareDensitySample c ⟨.south,true⟩ R.val
    (if upper then squareMidpointParameter M v else squareMidpointParameter M v-1)
  let weighted := fun v => (⟨scaleRat ((M:Rat)⁻¹) (f v).val,scaleRat_valid (f v).property⟩ : Scalar)
  have hp (v : Nat) : (k:Rat)-2+squareMidpointParameter M v=
      (if upper then squareMidpointParameter M v else squareMidpointParameter M v-1) := by
    cases upper <;> dsimp [k] <;> grind only
  have he : ∀ v,
      (rectangleGridHorizontal (rationalRiccatiKernelSample c) (squareFrameTile R k 1) M v 0).val.Equiv
        (weighted v).val := by
    intro v
    have hb := squareFrame_inner_bottom_weighted_sample c R M k v hM
    rw [hp] at hb
    simpa only [Rat.div_def,Rat.one_mul] using hb
  have ha := gridScalarSum_congr M _ weighted he
  have hb := gridScalarSum_scale ((M:Rat)⁻¹) f M
  exact equiv_trans
    (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M k 1).property
    (gridScalarSum M weighted).property
    (cartesianHalfEdgeSum c .south R.val M upper).property ha hb

theorem squareFrame_inner_bottom_tile_original_agreement (c : Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) (upper : Bool) :
    (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (if upper then 2 else 1) 1).val.Equiv
      (pairedSquareHalfEdgeSum c ⟨.south,upper⟩ R.val M) :=
  equiv_trans
    (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (if upper then 2 else 1) 1).property
    (cartesianHalfEdgeSum c .south R.val M upper).property
    (pairedSquareHalfEdgeSum_valid c ⟨.south,upper⟩ R.val M)
    (squareFrame_inner_bottom_tile_sum c R M hM upper)
    (cartesianHalfEdgeSum_agreement c .south R.val M hM upper)

theorem squareFrame_inner_bottom_full_edge_agreement (c : Scalar) (R : QPos)
    (M : Nat) (hM : 0<M) :
    (gridScalarSum 2 (fun k => squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (1+k) 1)).val.Equiv
      (add (pairedSquareHalfEdgeSum c ⟨.south,false⟩ R.val M)
        (pairedSquareHalfEdgeSum c ⟨.south,true⟩ R.val M)) := by
  have hl := squareFrame_inner_bottom_tile_original_agreement c R M hM false
  have hu := squareFrame_inner_bottom_tile_original_agreement c R M hM true
  have hs := add_equiv hl hu
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (gridScalarSum 2 (fun k => squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (1+k) 1)).property)
    (hright := add_valid (pairedSquareHalfEdgeSum_valid c ⟨.south,false⟩ R.val M)
      (pairedSquareHalfEdgeSum_valid c ⟨.south,true⟩ R.val M))
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := add_valid
      (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M 1 1).property
      (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M 2 1).property)
    (hright := add_valid (pairedSquareHalfEdgeSum_valid c ⟨.south,false⟩ R.val M)
      (pairedSquareHalfEdgeSum_valid c ⟨.south,true⟩ R.val M)) hs
  change gridScalarValue (gridScalarSum 2 _)=_
  rw [gridScalarSum_value]
  simp only [gridValueSum,Nat.add_zero] 
  rw [←hv,ComplexRawQuotient.ofRaw_add]
  change (0+gridScalarValue (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M 1 1))+
    gridScalarValue (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M 2 1)=
      gridScalarValue (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M 1 1)+
      gridScalarValue (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M 2 1)
  grind only

theorem gridScalarSum_bounded_congr (f g : Nat → Scalar) (M : Nat)
    (h : ∀ v, v<M → (f v).val.Equiv (g v).val) :
    (gridScalarSum M f).val.Equiv (gridScalarSum M g).val := by
  induction M with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ M ih => exact add_equiv (ih (fun v hv => h v (by omega))) (h M (by omega))

theorem gridScalarSum_reflected_parameters (f : Rat → Scalar) (M : Nat) (hM : 0<M) :
    (gridScalarSum M (fun v => f (1-squareMidpointParameter M v))).val.Equiv
      (gridScalarSum M (fun v => f (squareMidpointParameter M v))).val := by
  have he := gridScalarSum_bounded_congr
    (fun v => f (1-squareMidpointParameter M v))
    (fun v => f (squareMidpointParameter M (M-1-v))) M (by
      intro v hv
      rw [squareMidpointParameter_reverse M v hM hv]
      exact equiv_refl _ (f (1-squareMidpointParameter M v)).property)
  exact equiv_trans (gridScalarSum M (fun v => f (1-squareMidpointParameter M v))).property
    (gridScalarSum M (fun v => f (squareMidpointParameter M (M-1-v)))).property
    (gridScalarSum M (fun v => f (squareMidpointParameter M v))).property he
    (gridScalarSum_reverse (fun v => f (squareMidpointParameter M v)) M)

end ComputableAnalysis.ModularForms

