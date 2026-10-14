import ComputableAnalysis.RiemannHilbert.ContourSplitLimitLaws

/-! Actual rectangle boundary computations assembled from certified edges.
Their finite sums agree with the earlier holomorphic rectangle sampler. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

structure RectangleBoundaryDomains (f : DomainFunctions.Map) (J : QInterval × QInterval) : Prop where
  bottom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle J.1 J.2.lo) z → f.domain z
  top : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle J.1 J.2.hi) z → f.domain z
  left : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle J.2 J.1.lo) z → f.domain z
  right : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle J.2 J.1.hi) z → f.domain z

def rectangleBoundaryDomains_of_rectangle (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z) : RectangleBoundaryDomains f J where
  bottom := fun z hz => hdom z (representedRectangle_subrectangle J (horizontalIntervalRectangle J.1 J.2.lo) z Rat.le_refl Rat.le_refl Rat.le_refl hY hz)
  top := fun z hz => hdom z (representedRectangle_subrectangle J (horizontalIntervalRectangle J.1 J.2.hi) z Rat.le_refl Rat.le_refl hY Rat.le_refl hz)
  left := fun z hz => hdom z (representedRectangle_subrectangle J (verticalIntervalRectangle J.2 J.1.lo) z Rat.le_refl hX Rat.le_refl Rat.le_refl hz)
  right := fun z hz => hdom z (representedRectangle_subrectangle J (verticalIntervalRectangle J.2 J.1.hi) z hX Rat.le_refl Rat.le_refl Rat.le_refl hz)

def rectangleEdgeBoundary (b t r l : Scalar) : Scalar := scalarSum (gridScalarSub b t) (gridScalarSub r l)

def continuousRectangleBoundary (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : RectangleBoundaryDomains f J) (n : Nat) : Scalar :=
  rectangleEdgeBoundary (horizontalContinuousPrefix f J.1 J.2.lo hd.bottom n)
    (horizontalContinuousPrefix f J.1 J.2.hi hd.top n)
    (verticalContinuousPrefix f J.2 J.1.hi hd.right n)
    (verticalContinuousPrefix f J.2 J.1.lo hd.left n)

theorem rectangleGridHorizontalPoint_bottom (J : QInterval × QInterval) (M j : Nat) :
    rectangleGridHorizontalPoint J M j 0=⟨intervalGridTag J.1 M j,J.2.lo⟩ := by
  simp only [rectangleGridHorizontalPoint,intervalGridTag,intervalGridStep,
    rectangleGridStepX,rectangleGridStepY]
  simp [Rat.zero_mul,Rat.add_zero]

theorem rectangleGridHorizontalPoint_top (J : QInterval × QInterval) (M j : Nat) (hM : 0<M) :
    rectangleGridHorizontalPoint J M j M=⟨intervalGridTag J.1 M j,J.2.hi⟩ := by
  have he := Rat.div_mul_cancel (a := J.2.width) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  simp only [rectangleGridHorizontalPoint,intervalGridTag,intervalGridStep,
    rectangleGridStepX,rectangleGridStepY]
  rw [Rat.mul_comm (M:Rat),he]
  congr 1
  unfold QInterval.width
  grind only

theorem rectangleGridVerticalPoint_left (J : QInterval × QInterval) (M k : Nat) :
    rectangleGridVerticalPoint J M 0 k=⟨J.1.lo,intervalGridTag J.2 M k⟩ := by
  simp only [rectangleGridVerticalPoint,intervalGridTag,intervalGridStep,
    rectangleGridStepX,rectangleGridStepY]
  simp [Rat.zero_mul,Rat.add_zero]

theorem rectangleGridVerticalPoint_right (J : QInterval × QInterval) (M k : Nat) (hM : 0<M) :
    rectangleGridVerticalPoint J M M k=⟨J.1.hi,intervalGridTag J.2 M k⟩ := by
  have he := Rat.div_mul_cancel (a := J.1.width) (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))
  simp only [rectangleGridVerticalPoint,intervalGridTag,intervalGridStep,
    rectangleGridStepX,rectangleGridStepY]
  rw [Rat.mul_comm (M:Rat),he]
  congr 1
  unfold QInterval.width
  grind only

theorem holomorphicSample_horizontal_edge (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (y t : Rat) (ht : J.1.lo≤t ∧ t≤J.1.hi) (hy : J.2.lo≤y ∧ y≤J.2.hi)
    (hd : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle J.1 y) z → f.domain z) :
    holomorphicRectangleSample f hf J hdom ⟨t,y⟩ ≈ horizontalIntervalSample f J.1 y hd t := by
  have hq : rationalRectangleContains J ⟨t,y⟩ := ⟨ht.1,ht.2,hy.1,hy.2⟩
  have he : rationalRectangleContains (horizontalIntervalRectangle J.1 y) ⟨t,y⟩ :=
    ⟨ht.1,ht.2,Rat.le_refl,Rat.le_refl⟩
  have hz := hdom _ (rationalRectangle_represented_mem J _ hq)
  exact Setoid.trans (equiv_symm (holomorphicRectangleSample_agreement f hf J hdom _ hq hz))
    (Setoid.symm (continuousRectangleSample_agreement f _ hd _ he hz))

theorem holomorphicSample_vertical_edge (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (x t : Rat) (hx : J.1.lo≤x ∧ x≤J.1.hi) (ht : J.2.lo≤t ∧ t≤J.2.hi)
    (hd : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle J.2 x) z → f.domain z) :
    holomorphicRectangleSample f hf J hdom ⟨x,t⟩ ≈ verticalIntervalSample f J.2 x hd t := by
  have hq : rationalRectangleContains J ⟨x,t⟩ := ⟨hx.1,hx.2,ht.1,ht.2⟩
  have he : rationalRectangleContains (verticalIntervalRectangle J.2 x) ⟨x,t⟩ :=
    ⟨Rat.le_refl,Rat.le_refl,ht.1,ht.2⟩
  have hz := hdom _ (rationalRectangle_represented_mem J _ hq)
  exact Setoid.trans (equiv_symm (holomorphicRectangleSample_agreement f hf J hdom _ hq hz))
    (Setoid.symm (continuousRectangleSample_agreement f _ hd _ he hz))

theorem holomorphicRectangleBoundary_edges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hd : RectangleBoundaryDomains f J) (n : Nat) :
    holomorphicRectangleGridBoundary f hf J hdom n ≈ continuousRectangleBoundary f J hd n := by
  let M := 2^n
  let s := holomorphicRectangleSample f hf J hdom
  have hM : 0<M := Nat.two_pow_pos n
  have hB : gridScalarSum M (fun j => rectangleGridHorizontal s J M j 0) ≈
      horizontalContinuousPrefix f J.1 J.2.lo hd.bottom n := by
    apply gridScalarSum_congr_bounded M
    intro j hj
    unfold rectangleGridHorizontal
    rw [rectangleGridHorizontalPoint_bottom]
    exact Setoid.trans (horizontalInterval_weight _ _)
      (scaleRat_equiv (holomorphicSample_horizontal_edge f hf J hdom J.2.lo _
        (intervalGridTag_mem_interval J.1 M j hX hM hj) ⟨Rat.le_refl,hY⟩ hd.bottom))
  have hT : gridScalarSum M (fun j => rectangleGridHorizontal s J M j M) ≈
      horizontalContinuousPrefix f J.1 J.2.hi hd.top n := by
    apply gridScalarSum_congr_bounded M
    intro j hj
    unfold rectangleGridHorizontal
    rw [rectangleGridHorizontalPoint_top J M j hM]
    exact Setoid.trans (horizontalInterval_weight _ _)
      (scaleRat_equiv (holomorphicSample_horizontal_edge f hf J hdom J.2.hi _
        (intervalGridTag_mem_interval J.1 M j hX hM hj) ⟨hY,Rat.le_refl⟩ hd.top))
  have ver (j : Nat) (x : Rat) (hx : J.1.lo≤x ∧ x≤J.1.hi)
      (he : ∀ k, rectangleGridVerticalPoint J M j k=⟨x,intervalGridTag J.2 M k⟩)
      (hv : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle J.2 x) z → f.domain z) :
      gridScalarSum M (fun k => rectangleGridVertical s J M j k) ≈ verticalContinuousPrefix f J.2 x hv n := by
    apply Setoid.trans (b := gridScalarSum M (fun k => scalarProduct (rationalRectangleScalar ⟨0,1⟩)
      (RadialLogarithmChains.scale (intervalGridStep J.2 M) (verticalIntervalSample f J.2 x hv (intervalGridTag J.2 M k)))))
    · apply gridScalarSum_congr_bounded M
      intro k hk
      unfold rectangleGridVertical
      rw [he k]
      have hs := holomorphicSample_vertical_edge f hf J hdom x _ hx
        (intervalGridTag_mem_interval J.2 M k hY hM hk) hv
      exact Setoid.trans (verticalInterval_weight _ _) (mul_equiv (ofQComplex_valid _) (ofQComplex_valid _)
        (scaleRat_valid (s _).property) (scaleRat_valid (verticalIntervalSample f J.2 x hv _).property)
        (equiv_refl _ (ofQComplex_valid _)) (scaleRat_equiv hs))
    · exact gridScalarSum_product_left M _ _
  have hL := ver 0 J.1.lo ⟨Rat.le_refl,hX⟩ (rectangleGridVerticalPoint_left J M) hd.left
  have hR := ver M J.1.hi ⟨hX,Rat.le_refl⟩ (fun k => rectangleGridVerticalPoint_right J M k hM) hd.right
  exact add_equiv
    (Setoid.trans (gridScalarSum_sub_agreement M (fun j => rectangleGridHorizontal s J M j 0)
      (fun j => rectangleGridHorizontal s J M j M)) (FunctionTheory.sub_congr hB hT))
    (Setoid.trans (gridScalarSum_sub_agreement M (fun k => rectangleGridVertical s J M M k)
      (fun k => rectangleGridVertical s J M 0 k)) (FunctionTheory.sub_congr hR hL))

theorem continuousRectangleBoundary_eventual_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hd : RectangleBoundaryDomains f J) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (continuousRectangleBoundary f J hd n).val eps.val := by
  obtain ⟨N,hN⟩ := holomorphicRectangleGridBoundary_converges_zero f hf J hdom hX hY eps
  exact ⟨N,fun n hn => Small.congr (holomorphicRectangleGridBoundary f hf J hdom n).property
    (continuousRectangleBoundary f J hd n).property (holomorphicRectangleBoundary_edges f hf J hX hY hdom hd n) (hN n hn)⟩

end ComputableAnalysis.RiemannHilbert.RectangularContour
