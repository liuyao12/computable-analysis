import ComputableAnalysis.RiemannHilbert.ContourRibbonAssembly

/-! Actual displaced rectangle boundaries agree through the four pole-free
ribbon rectangles. No boundary limit or deformation identity is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem ribbonTileSum_eventual_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (G : RectangleRibbon) (hd : RibbonDomain f G) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (ribbonTileSum f G hd n).val eps.val := by
  let eta := divideRadius eps (⟨4,by decide +kernel⟩ : QPos)
  obtain ⟨L,hL⟩ := continuousRectangleBoundary_eventual_zero f hf (ribbonLeft G) G.xLo
    (ribbon_outer_y_order G) (ribbon_left_domain f G hd) (ribbonLeftDomains f G hd) eta
  obtain ⟨R,hR⟩ := continuousRectangleBoundary_eventual_zero f hf (ribbonRight G) G.xHi
    (ribbon_outer_y_order G) (ribbon_right_domain f G hd) (ribbonRightDomains f G hd) eta
  obtain ⟨B,hB⟩ := continuousRectangleBoundary_eventual_zero f hf (ribbonBottom G) G.xOrder
    G.yLo (ribbon_bottom_domain f G hd) (ribbonBottomDomains f G hd) eta
  obtain ⟨T,hT⟩ := continuousRectangleBoundary_eventual_zero f hf (ribbonTop G) G.xOrder
    G.yHi (ribbon_top_domain f G hd) (ribbonTopDomains f G hd) eta
  refine ⟨max (max L R) (max B T), ?_⟩
  intro n hn
  have hs := LocalODE.small_add (LocalODE.small_add (hL n (by omega)) (hR n (by omega)))
    (LocalODE.small_add (hB n (by omega)) (hT n (by omega)))
  have he : (eta.val+eta.val)+(eta.val+eta.val)=eps.val := by
    have h := divideRadius_identity eps (⟨4,by decide +kernel⟩ : QPos)
    change 4*eta.val=eps.val at h
    grind only
  rw [he] at hs
  exact hs

theorem ribbonSplitCorrection_eventual_zero (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (G : RectangleRibbon) (hd : RibbonDomain f G) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (ribbonSplitCorrection f G hd n).val eps.val := by
  let eta := divideRadius eps (⟨4,by decide +kernel⟩ : QPos)
  obtain ⟨B,hB⟩ := horizontalTripleSplitError_eventual_zero f hc G.outer.1 G.outer.2.lo
    (ribbonOuterDomains f G hd).bottom G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi eta
  obtain ⟨T,hT⟩ := horizontalTripleSplitError_eventual_zero f hc G.outer.1 G.outer.2.hi
    (ribbonOuterDomains f G hd).top G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi eta
  obtain ⟨L,hL⟩ := verticalTripleSplitError_eventual_zero f hc G.outer.2 G.inner.1.lo
    (ribbonLeftDomains f G hd).right G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi eta
  obtain ⟨R,hR⟩ := verticalTripleSplitError_eventual_zero f hc G.outer.2 G.inner.1.hi
    (ribbonRightDomains f G hd).left G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi eta
  refine ⟨max (max B T) (max L R), ?_⟩
  intro n hn
  have hs := SeriesLimitLaws.small_sub (SeriesLimitLaws.small_sub (hB n (by omega)) (hT n (by omega)))
    (SeriesLimitLaws.small_sub (hL n (by omega)) (hR n (by omega)))
  have he : (eta.val+eta.val)+(eta.val+eta.val)=eps.val := by
    have h := divideRadius_identity eps (⟨4,by decide +kernel⟩ : QPos)
    change 4*eta.val=eps.val at h
    grind only
  rw [he] at hs
  exact hs

theorem ribbonDifference_eventual_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (G : RectangleRibbon) (hd : RibbonDomain f G) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (ribbonDifference f G hd n).val eps.val := by
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  obtain ⟨A,hA⟩ := ribbonTileSum_eventual_zero f hf G hd eta
  obtain ⟨B,hB⟩ := ribbonSplitCorrection_eventual_zero f hf.continuous G hd eta
  refine ⟨max A B, ?_⟩
  intro n hn
  have hs := LocalODE.small_add (hA n (by omega)) (hB n (by omega))
  have he : eta.val+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at h
    grind only
  rw [he] at hs
  exact Small.congr (scalarSum (ribbonTileSum f G hd n) (ribbonSplitCorrection f G hd n)).property
    (ribbonDifference f G hd n).property (equiv_symm (ribbonDifference_assembly f G hd n)) hs

theorem ribbonDifference_converges_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (G : RectangleRibbon) (hd : RibbonDomain f G) :
    Converges (ribbonDifference f G hd) (rationalRectangleScalar QComplex.zero) :=
  converge_zero _ (ribbonDifference_eventual_zero f hf G hd)

theorem ribbonBoundary_limits_agree (f : DomainFunctions.Map) (hf : Holomorphic f)
    (G : RectangleRibbon) (hd : RibbonDomain f G) (a b : Scalar)
    (ha : Converges (ribbonOuterBoundary f G hd) a)
    (hb : Converges (ribbonInnerBoundary f G hd) b) : a≈b := by
  exact converge_unique _ a b ha (converge_perturbation _ _ b hb
    (ribbonDifference_eventual_zero f hf G hd))

end ComputableAnalysis.RiemannHilbert.RectangularContour
