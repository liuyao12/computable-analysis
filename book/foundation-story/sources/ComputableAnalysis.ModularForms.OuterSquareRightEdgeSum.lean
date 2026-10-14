import ComputableAnalysis.ModularForms.OuterHalfEdgeConcatenation

/-! Outer right-side tiles assemble into doubled east half-edge sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem squareFrame_outer_right_tile_sum (c : Scalar) (R : QPos) (M a : Nat)
    (hM : 0<M) (upper : Bool) :
    (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 4 ((if upper then 2 else 0)+a)).val.Equiv
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
        (if upper then ((a:Rat)+u)/2 else ((a:Rat)+u)/2-1)) M (((2*M:Nat):Rat)⁻¹)).val := by
  let k := (if upper then 2 else 0)+a
  let f := fun v => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
    (if upper then ((a:Rat)+squareMidpointParameter M v)/2 else ((a:Rat)+squareMidpointParameter M v)/2-1)
  let weighted := fun v => (⟨scaleRat (((2*M:Nat):Rat)⁻¹) (f v).val,scaleRat_valid (f v).property⟩ : Scalar)
  have hp (v : Nat) : ((k:Rat)-2+squareMidpointParameter M v)/2=
      (if upper then ((a:Rat)+squareMidpointParameter M v)/2 else ((a:Rat)+squareMidpointParameter M v)/2-1) := by
    cases upper <;> dsimp [k] <;> simp only [Rat.natCast_add] <;>
      change _=_ <;> grind only
  have hr : 1/(2*(M:Rat))=((2*M:Nat):Rat)⁻¹ := by
    rw [Rat.natCast_mul]
    change 1/(2*(M:Rat))=(2*(M:Rat))⁻¹
    rw [Rat.div_def,Rat.one_mul]
  have he : ∀ v,
      (rectangleGridVertical (rationalRiccatiKernelSample c) (squareFrameTile R 4 k) M 0 v).val.Equiv
        (weighted v).val := by
    intro v
    rw [←squareFrameTile_shared_vertical_samples (rationalRiccatiKernelSample c) R M 3 k v hM]
    have hb := squareFrame_outer_right_weighted_sample c R M k v hM
    rw [hp,hr] at hb
    exact hb
  have ha := gridScalarSum_congr M _ weighted he
  have hb := gridScalarSum_scale (((2*M:Nat):Rat)⁻¹) f M
  exact equiv_trans (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 4 k).property
    (gridScalarSum M weighted).property
    (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
      (if upper then ((a:Rat)+u)/2 else ((a:Rat)+u)/2-1)) M (((2*M:Nat):Rat)⁻¹)).property ha hb

theorem squareFrame_outer_right_half_sum (c : Scalar) (R : QPos) (M : Nat)
    (hM : 0<M) (upper : Bool) :
    (scalarSum
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 4 (if upper then 2 else 0))
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 4 ((if upper then 2 else 0)+1))).val.Equiv
      (pairedSquareHalfEdgeSum c ⟨.east,upper⟩ (2*R.val) (2*M)) := by
  have h0 := squareFrame_outer_right_tile_sum c R M 0 hM upper
  have h1 := squareFrame_outer_right_tile_sum c R M 1 hM upper
  simp only [Nat.add_zero] at h0
  change (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 4 (if upper then 2 else 0)).val.Equiv
    (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
      (if upper then (0+u)/2 else (0+u)/2-1)) M (((2*M:Nat):Rat)⁻¹)).val at h0
  change (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 4 ((if upper then 2 else 0)+1)).val.Equiv
    (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
      (if upper then (1+u)/2 else (1+u)/2-1)) M (((2*M:Nat):Rat)⁻¹)).val at h1
  simp only [Rat.zero_add] at h0
  have ha := add_equiv h0 h1
  have hb := cartesianHalfEdgeSum_split c .east (2*R.val) M hM upper
  have hc := cartesianHalfEdgeSum_agreement c .east (2*R.val) (2*M) (by omega) upper
  exact equiv_trans
    (scalarSum (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 4 (if upper then 2 else 0))
      (squareFrameVerticalEdge (rationalRiccatiKernelSample c) R M 4 ((if upper then 2 else 0)+1))).property
    (scalarSum
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
        (if upper then u/2 else u/2-1)) M (((2*M:Nat):Rat)⁻¹))
      (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
        (if upper then (1+u)/2 else (1+u)/2-1)) M (((2*M:Nat):Rat)⁻¹))).property
    (pairedSquareHalfEdgeSum_valid c ⟨.east,upper⟩ (2*R.val) (2*M)) ha
    (equiv_trans
      (scalarSum
        (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
          (if upper then u/2 else u/2-1)) M (((2*M:Nat):Rat)⁻¹))
        (weightedMidpointSum (fun u => pairedSquareDensitySample c ⟨.east,true⟩ (2*R.val)
          (if upper then (1+u)/2 else (1+u)/2-1)) M (((2*M:Nat):Rat)⁻¹))).property
      (cartesianHalfEdgeSum c .east (2*R.val) (2*M) upper).property
      (pairedSquareHalfEdgeSum_valid c ⟨.east,upper⟩ (2*R.val) (2*M)) hb hc)

end ComputableAnalysis.ModularForms
