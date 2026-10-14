import ComputableAnalysis.RiemannHilbert.ContourBoundaryEdges

/-! One executable sampler for the four certified boundary edges, without
requiring function membership inside the rectangle. Actual finite sums agree. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def rationalRectangleBoundaryContains (J : QInterval × QInterval) (q : QComplex) : Prop :=
  rationalRectangleContains (horizontalIntervalRectangle J.1 J.2.lo) q ∨
  rationalRectangleContains (horizontalIntervalRectangle J.1 J.2.hi) q ∨
  rationalRectangleContains (verticalIntervalRectangle J.2 J.1.lo) q ∨
  rationalRectangleContains (verticalIntervalRectangle J.2 J.1.hi) q

def rectangleBoundarySample (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : RectangleBoundaryDomains f J) (q : QComplex) : Scalar :=
  if hb : rationalRectangleContains (horizontalIntervalRectangle J.1 J.2.lo) q then
    f.eval (rationalRectangleScalar q) (hd.bottom _ (rationalRectangle_represented_mem _ q hb))
  else if ht : rationalRectangleContains (horizontalIntervalRectangle J.1 J.2.hi) q then
    f.eval (rationalRectangleScalar q) (hd.top _ (rationalRectangle_represented_mem _ q ht))
  else if hl : rationalRectangleContains (verticalIntervalRectangle J.2 J.1.lo) q then
    f.eval (rationalRectangleScalar q) (hd.left _ (rationalRectangle_represented_mem _ q hl))
  else if hr : rationalRectangleContains (verticalIntervalRectangle J.2 J.1.hi) q then
    f.eval (rationalRectangleScalar q) (hd.right _ (rationalRectangle_represented_mem _ q hr))
  else rationalRectangleScalar QComplex.zero

theorem rectangleBoundarySample_value (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : RectangleBoundaryDomains f J) (q : QComplex) (hq : rationalRectangleBoundaryContains J q)
    (hz : f.domain (rationalRectangleScalar q)) : rectangleBoundarySample f J hd q≈f.eval _ hz := by
  unfold rectangleBoundarySample
  split
  · exact equiv_refl _ (f.eval _ hz).property
  · split
    · exact equiv_refl _ (f.eval _ hz).property
    · split
      · exact equiv_refl _ (f.eval _ hz).property
      · split
        · exact equiv_refl _ (f.eval _ hz).property
        · unfold rationalRectangleBoundaryContains at hq
          rcases hq with hq|hq|hq|hq <;> contradiction

theorem boundarySample_horizontal_edge (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (s : QComplex → Scalar)
    (hs : ∀ q, rationalRectangleBoundaryContains J q → ∀ hz, s q≈f.eval (rationalRectangleScalar q) hz)
    (y t : Rat) (ht : J.1.lo≤t ∧ t≤J.1.hi) (hy : y=J.2.lo ∨ y=J.2.hi)
    (hd : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle J.1 y) z → f.domain z) :
    s ⟨t,y⟩≈horizontalIntervalSample f J.1 y hd t := by
  have he : rationalRectangleContains (horizontalIntervalRectangle J.1 y) ⟨t,y⟩ :=
    ⟨ht.1,ht.2,Rat.le_refl,Rat.le_refl⟩
  have hq : rationalRectangleBoundaryContains J ⟨t,y⟩ := by
    rcases hy with hy|hy
    · subst y; exact Or.inl he
    · subst y; exact Or.inr (Or.inl he)
  exact Setoid.trans (hs _ hq (hd _ (rationalRectangle_represented_mem _ _ he)))
    (equiv_symm (continuousRectangleSample_agreement f _ hd _ he _))

theorem boundarySample_vertical_edge (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (s : QComplex → Scalar)
    (hs : ∀ q, rationalRectangleBoundaryContains J q → ∀ hz, s q≈f.eval (rationalRectangleScalar q) hz)
    (x t : Rat) (ht : J.2.lo≤t ∧ t≤J.2.hi) (hx : x=J.1.lo ∨ x=J.1.hi)
    (hd : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle J.2 x) z → f.domain z) :
    s ⟨x,t⟩≈verticalIntervalSample f J.2 x hd t := by
  have he : rationalRectangleContains (verticalIntervalRectangle J.2 x) ⟨x,t⟩ :=
    ⟨Rat.le_refl,Rat.le_refl,ht.1,ht.2⟩
  have hq : rationalRectangleBoundaryContains J ⟨x,t⟩ := by
    rcases hx with hx|hx
    · subst x; exact Or.inr (Or.inr (Or.inl he))
    · subst x; exact Or.inr (Or.inr (Or.inr he))
  exact Setoid.trans (hs _ hq (hd _ (rationalRectangle_represented_mem _ _ he)))
    (equiv_symm (continuousRectangleSample_agreement f _ hd _ he _))

theorem rectangleGridBoundary_edges (f : DomainFunctions.Map)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) (s : QComplex → Scalar)
    (hs : ∀ q, rationalRectangleBoundaryContains J q → ∀ hz, s q≈f.eval (rationalRectangleScalar q) hz)
    (n : Nat) : rectangleGridBoundary s J (2^n)≈continuousRectangleBoundary f J hd n := by
  let M := 2^n
  have hM : 0<M := Nat.two_pow_pos n
  have hB : gridScalarSum M (fun j => rectangleGridHorizontal s J M j 0) ≈
      horizontalContinuousPrefix f J.1 J.2.lo hd.bottom n := by
    apply gridScalarSum_congr_bounded M
    intro j hj
    unfold rectangleGridHorizontal
    rw [rectangleGridHorizontalPoint_bottom]
    exact Setoid.trans (horizontalInterval_weight _ _)
      (scaleRat_equiv (boundarySample_horizontal_edge f J s hs J.2.lo _
        (intervalGridTag_mem_interval J.1 M j hX hM hj) (Or.inl rfl) hd.bottom))
  have hT : gridScalarSum M (fun j => rectangleGridHorizontal s J M j M) ≈
      horizontalContinuousPrefix f J.1 J.2.hi hd.top n := by
    apply gridScalarSum_congr_bounded M
    intro j hj
    unfold rectangleGridHorizontal
    rw [rectangleGridHorizontalPoint_top J M j hM]
    exact Setoid.trans (horizontalInterval_weight _ _)
      (scaleRat_equiv (boundarySample_horizontal_edge f J s hs J.2.hi _
        (intervalGridTag_mem_interval J.1 M j hX hM hj) (Or.inr rfl) hd.top))
  have ver (j : Nat) (x : Rat) (hx : x=J.1.lo ∨ x=J.1.hi)
      (he : ∀ k, rectangleGridVerticalPoint J M j k=⟨x,intervalGridTag J.2 M k⟩)
      (hv : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle J.2 x) z → f.domain z) :
      gridScalarSum M (fun k => rectangleGridVertical s J M j k) ≈ verticalContinuousPrefix f J.2 x hv n := by
    apply Setoid.trans (b := gridScalarSum M (fun k => scalarProduct (rationalRectangleScalar ⟨0,1⟩)
      (RadialLogarithmChains.scale (intervalGridStep J.2 M) (verticalIntervalSample f J.2 x hv (intervalGridTag J.2 M k)))))
    · apply gridScalarSum_congr_bounded M
      intro k hk
      unfold rectangleGridVertical
      rw [he k]
      have hs := boundarySample_vertical_edge f J s hs x _
        (intervalGridTag_mem_interval J.2 M k hY hM hk) hx hv
      exact Setoid.trans (verticalInterval_weight _ _) (mul_equiv (ofQComplex_valid _) (ofQComplex_valid _)
        (scaleRat_valid (s _).property) (scaleRat_valid (verticalIntervalSample f J.2 x hv _).property)
        (equiv_refl _ (ofQComplex_valid _)) (scaleRat_equiv hs))
    · exact gridScalarSum_product_left M _ _
  have hL := ver 0 J.1.lo (Or.inl rfl) (rectangleGridVerticalPoint_left J M) hd.left
  have hR := ver M J.1.hi (Or.inr rfl) (fun k => rectangleGridVerticalPoint_right J M k hM) hd.right
  exact add_equiv
    (Setoid.trans (gridScalarSum_sub_agreement M (fun j => rectangleGridHorizontal s J M j 0)
      (fun j => rectangleGridHorizontal s J M j M)) (FunctionTheory.sub_congr hB hT))
    (Setoid.trans (gridScalarSum_sub_agreement M (fun k => rectangleGridVertical s J M M k)
      (fun k => rectangleGridVertical s J M 0 k)) (FunctionTheory.sub_congr hR hL))

theorem rectangleBoundarySample_edges (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (hd : RectangleBoundaryDomains f J) (n : Nat) :
    rectangleGridBoundary (rectangleBoundarySample f J hd) J (2^n)≈continuousRectangleBoundary f J hd n :=
  rectangleGridBoundary_edges f J hX hY hd _ (rectangleBoundarySample_value f J hd) n

end ComputableAnalysis.RiemannHilbert.RectangularContour
