import ComputableAnalysis.ModularForms.OuterSquareBottomEdgeSum

/-! Reversed and signed outer top and left tile pieces. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squareFrame_outer_top_tile_sum (c : Scalar) (R : QPos) (M a : Nat)
    (hM : 0<M) (ha : a≤1) (upper : Bool) :
    (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M ((if upper then 0 else 2)+(1-a)) 4).val.Equiv
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.north,true⟩ (2*R.val)
        (if upper then ((a:Rat)+u)/2 else ((a:Rat)+u)/2-1)) M (-1/((2*M:Nat):Rat))).val := by
  let k := (if upper then 0 else 2)+(1-a)
  let F := fun u => pairedSquareDensitySample c ⟨.north,true⟩ (2*R.val)
    (if upper then ((a:Rat)+u)/2 else ((a:Rat)+u)/2-1)
  let f := fun v => F (1-squareMidpointParameter M v)
  let g := fun v => F (squareMidpointParameter M v)
  let weighted := fun v => (⟨scaleRat (-1/((2*M:Nat):Rat)) (f v).val,scaleRat_valid (f v).property⟩ : Scalar)
  have hi : a+(1-a)=1 := by omega
  have hc := congrArg (fun v : Nat => (v:Rat)) hi
  simp only [Rat.natCast_add] at hc
  change (a:Rat)+((1-a:Nat):Rat)=1 at hc
  have hp (v : Nat) : (2-(k:Rat)-squareMidpointParameter M v)/2=
      (if upper then ((a:Rat)+(1-squareMidpointParameter M v))/2 else ((a:Rat)+(1-squareMidpointParameter M v))/2-1) := by
    cases upper <;> dsimp [k] <;> simp only [Rat.natCast_add] <;> grind only
  have hr : -1/(2*(M:Rat))= -1/((2*M:Nat):Rat) := by
    rw [Rat.natCast_mul]
    rfl
  have he : ∀ v,
      (rectangleGridHorizontal (rationalRiccatiKernelSample c) (squareFrameTile R k 4) M v 0).val.Equiv
        (weighted v).val := by
    intro v
    rw [←squareFrameTile_shared_horizontal_samples (rationalRiccatiKernelSample c) R M k 3 v hM]
    have hb := squareFrame_outer_top_weighted_sample c R M k v hM
    rw [hp,hr] at hb
    exact hb
  have hA := gridScalarSum_congr M _ weighted he
  have hB := gridScalarSum_scale (-1/((2*M:Nat):Rat)) f M
  have hC := representedScale_congr (gridScalarSum M f) (gridScalarSum M g) (-1/((2*M:Nat):Rat))
    (gridScalarSum_reflected_parameters F M hM)
  exact equiv_trans (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M k 4).property
    (gridScalarSum M weighted).property
    (weightedMidpointSum F M (-1/((2*M:Nat):Rat))).property hA
    (equiv_trans (gridScalarSum M weighted).property (scaleRat_valid (gridScalarSum M f).property)
      (weightedMidpointSum F M (-1/((2*M:Nat):Rat))).property hB hC)

theorem squareFrame_outer_left_tile_sum (c : Scalar) (R : QPos) (M a : Nat)
    (hM : 0<M) (ha : a≤1) (upper : Bool) :
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 0 ((if upper then 0 else 2)+(1-a))).val.Equiv
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.west,true⟩ (2*R.val)
        (if upper then ((a:Rat)+u)/2 else ((a:Rat)+u)/2-1)) M (-1/((2*M:Nat):Rat))).val := by
  let k := (if upper then 0 else 2)+(1-a)
  let F := fun u => pairedSquareDensitySample c ⟨.west,true⟩ (2*R.val)
    (if upper then ((a:Rat)+u)/2 else ((a:Rat)+u)/2-1)
  let f := fun v => F (1-squareMidpointParameter M v)
  let g := fun v => F (squareMidpointParameter M v)
  let weighted := fun v => (⟨scaleRat (-1/((2*M:Nat):Rat)) (f v).val,scaleRat_valid (f v).property⟩ : Scalar)
  have hi : a+(1-a)=1 := by omega
  have hc := congrArg (fun v : Nat => (v:Rat)) hi
  simp only [Rat.natCast_add] at hc
  change (a:Rat)+((1-a:Nat):Rat)=1 at hc
  have hp (v : Nat) : (2-(k:Rat)-squareMidpointParameter M v)/2=
      (if upper then ((a:Rat)+(1-squareMidpointParameter M v))/2 else ((a:Rat)+(1-squareMidpointParameter M v))/2-1) := by
    cases upper <;> dsimp [k] <;> simp only [Rat.natCast_add] <;> grind only
  have hr : -1/(2*(M:Rat))= -1/((2*M:Nat):Rat) := by
    rw [Rat.natCast_mul]
    rfl
  have he : ∀ v,
      (rectangleGridVertical (rationalRiccatiKernelSample c) (squareFrameTile R 0 k) M 0 v).val.Equiv
        (weighted v).val := by
    intro v
    have hb := squareFrame_outer_left_weighted_sample c R M k v hM
    rw [hp,hr] at hb
    exact hb
  have hA := gridScalarSum_congr M _ weighted he
  have hB := gridScalarSum_scale (-1/((2*M:Nat):Rat)) f M
  have hC := representedScale_congr (gridScalarSum M f) (gridScalarSum M g) (-1/((2*M:Nat):Rat))
    (gridScalarSum_reflected_parameters F M hM)
  exact equiv_trans (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 0 k).property
    (gridScalarSum M weighted).property
    (weightedMidpointSum F M (-1/((2*M:Nat):Rat))).property hA
    (equiv_trans (gridScalarSum M weighted).property (scaleRat_valid (gridScalarSum M f).property)
      (weightedMidpointSum F M (-1/((2*M:Nat):Rat))).property hB hC)

theorem negativeCartesianHalfEdgeSum_split (c : Scalar) (quarter : Quarter) (S : Rat)
    (M : Nat) (hM : 0<M) (upper : Bool) :
    (scalarSum
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨quarter,true⟩ S
        (if upper then u/2 else u/2-1)) M (-1/((2*M:Nat):Rat)))
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨quarter,true⟩ S
        (if upper then (1+u)/2 else (1+u)/2-1)) M (-1/((2*M:Nat):Rat)))).val.Equiv
      (negativeCartesianHalfEdgeSum c quarter S (2*M) upper).val := by
  have h := weightedSquareMidpointSum_concat
    (fun u => pairedSquareDensitySample c ⟨quarter,true⟩ S (if upper then u else u-1))
    M hM (-1/((2*M:Nat):Rat))
  exact h

theorem squareFrame_outer_top_half_sum (c : Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (upper : Bool) :
    (scalarSum (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M ((if upper then 0 else 2)+1) 4)
      (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (if upper then 0 else 2) 4)).val.Equiv
      (neg (pairedSquareHalfEdgeSum c ⟨.north,upper⟩ (2*R.val) (2*M))) := by
  let A := weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.north,true⟩ (2*R.val)
    (if upper then u/2 else u/2-1)) M (-1/((2*M:Nat):Rat))
  let B := weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.north,true⟩ (2*R.val)
    (if upper then (1+u)/2 else (1+u)/2-1)) M (-1/((2*M:Nat):Rat))
  have h0 := squareFrame_outer_top_tile_sum c R M 0 hM (by omega) upper
  have h1 := squareFrame_outer_top_tile_sum c R M 1 hM (by omega) upper
  simp only [Nat.sub_zero,Nat.sub_self,Nat.add_zero] at h0 h1
  change (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M ((if upper then 0 else 2)+1) 4).val.Equiv
    (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.north,true⟩ (2*R.val)
      (if upper then (0+u)/2 else (0+u)/2-1)) M (-1/((2*M:Nat):Rat))).val at h0
  change (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (if upper then 0 else 2) 4).val.Equiv B.val at h1
  simp only [Rat.zero_add] at h0
  have ha := add_equiv h0 h1
  have hb := negativeCartesianHalfEdgeSum_split c .north (2*R.val) M hM upper
  have hc := negativeCartesianHalfEdgeSum_agreement c .north (2*R.val) (2*M) (by omega) upper
  exact equiv_trans
    (scalarSum (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M ((if upper then 0 else 2)+1) 4)
      (squareFrameHorizontalEdge (rationalRiccatiKernelSample c) R M (if upper then 0 else 2) 4)).property
    (scalarSum A B).property
    (neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.north,upper⟩ (2*R.val) (2*M))) ha
    (equiv_trans (scalarSum A B).property
      (negativeCartesianHalfEdgeSum c .north (2*R.val) (2*M) upper).property
      (neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.north,upper⟩ (2*R.val) (2*M))) hb hc)

theorem squareFrame_outer_left_half_sum (c : Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (upper : Bool) :
    (scalarSum (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 0 ((if upper then 0 else 2)+1))
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 0 (if upper then 0 else 2))).val.Equiv
      (neg (pairedSquareHalfEdgeSum c ⟨.west,upper⟩ (2*R.val) (2*M))) := by
  let A := weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.west,true⟩ (2*R.val)
    (if upper then u/2 else u/2-1)) M (-1/((2*M:Nat):Rat))
  let B := weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.west,true⟩ (2*R.val)
    (if upper then (1+u)/2 else (1+u)/2-1)) M (-1/((2*M:Nat):Rat))
  have h0 := squareFrame_outer_left_tile_sum c R M 0 hM (by omega) upper
  have h1 := squareFrame_outer_left_tile_sum c R M 1 hM (by omega) upper
  simp only [Nat.sub_zero,Nat.sub_self,Nat.add_zero] at h0 h1
  change (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 0 ((if upper then 0 else 2)+1)).val.Equiv
    (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.west,true⟩ (2*R.val)
      (if upper then (0+u)/2 else (0+u)/2-1)) M (-1/((2*M:Nat):Rat))).val at h0
  change (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 0 (if upper then 0 else 2)).val.Equiv B.val at h1
  simp only [Rat.zero_add] at h0
  have ha := add_equiv h0 h1
  have hb := negativeCartesianHalfEdgeSum_split c .west (2*R.val) M hM upper
  have hc := negativeCartesianHalfEdgeSum_agreement c .west (2*R.val) (2*M) (by omega) upper
  exact equiv_trans
    (scalarSum (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 0 ((if upper then 0 else 2)+1))
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 0 (if upper then 0 else 2))).property
    (scalarSum A B).property
    (neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.west,upper⟩ (2*R.val) (2*M))) ha
    (equiv_trans (scalarSum A B).property
      (negativeCartesianHalfEdgeSum c .west (2*R.val) (2*M) upper).property
      (neg_valid (pairedSquareHalfEdgeSum_valid c ⟨.west,upper⟩ (2*R.val) (2*M))) hb hc)

end ComputableAnalysis.ModularForms
