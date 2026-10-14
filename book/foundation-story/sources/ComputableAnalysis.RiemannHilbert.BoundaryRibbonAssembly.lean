import ComputableAnalysis.RiemannHilbert.BoundaryCauchyOverlap

/-! Actual four-tile boundary assembly without interior kernel domains.
Only genuine tile-edge domains are supplied. Outer and inner edge domains,
finite cancellation and vanishing split corrections are derived. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryRibbon
open ComplexRaw FunctionTheory DomainFunctions RectangularContour
set_option autoImplicit false

structure Domains (f : DomainFunctions.Map) (G : RectangleRibbon) : Prop where
  left : RectangleBoundaryDomains f (ribbonLeft G)
  right : RectangleBoundaryDomains f (ribbonRight G)
  bottom : RectangleBoundaryDomains f (ribbonBottom G)
  top : RectangleBoundaryDomains f (ribbonTop G)

theorem ribbonLeftDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : RectangleBoundaryDomains f (ribbonLeft G) := hd.left
theorem ribbonRightDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : RectangleBoundaryDomains f (ribbonRight G) := hd.right
theorem ribbonBottomDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : RectangleBoundaryDomains f (ribbonBottom G) := hd.bottom
theorem ribbonTopDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : RectangleBoundaryDomains f (ribbonTop G) := hd.top

theorem ribbonOuterDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) :
    RectangleBoundaryDomains f G.outer := {
  bottom z hz := by
    rcases representedHorizontal_three_cover G.outer.1 G.outer.2.lo G.inner.1.lo G.inner.1.hi z hz with hL|hB|hR
    · exact hd.left.bottom z hL
    · exact hd.bottom.bottom z hB
    · exact hd.right.bottom z hR
  top z hz := by
    rcases representedHorizontal_three_cover G.outer.1 G.outer.2.hi G.inner.1.lo G.inner.1.hi z hz with hL|hT|hR
    · exact hd.left.top z hL
    · exact hd.top.top z hT
    · exact hd.right.top z hR
  left := hd.left.left
  right := hd.right.right
}

theorem ribbonInnerDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) :
    RectangleBoundaryDomains f G.inner := {
  bottom := hd.bottom.top
  top := hd.top.bottom
  left := verticalInterval_subdomain f G.outer.2 G.inner.2 G.inner.1.lo hd.left.right G.yLo G.yHi
  right := verticalInterval_subdomain f G.outer.2 G.inner.2 G.inner.1.hi hd.right.left G.yLo G.yHi
}

def ribbonOuterBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f G.outer (ribbonOuterDomains f G hd)
def ribbonInnerBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f G.inner (ribbonInnerDomains f G hd)
def ribbonLeftBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f (ribbonLeft G) (ribbonLeftDomains f G hd)
def ribbonRightBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f (ribbonRight G) (ribbonRightDomains f G hd)
def ribbonBottomBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f (ribbonBottom G) (ribbonBottomDomains f G hd)
def ribbonTopBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f (ribbonTop G) (ribbonTopDomains f G hd)

def ribbonTileSum (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) (n : Nat) : Scalar :=
  scalarSum (scalarSum (ribbonLeftBoundary f G hd n) (ribbonRightBoundary f G hd n))
    (scalarSum (ribbonBottomBoundary f G hd n) (ribbonTopBoundary f G hd n))
def ribbonDifference (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) (n : Nat) : Scalar :=
  gridScalarSub (ribbonOuterBoundary f G hd n) (ribbonInnerBoundary f G hd n)

def ribbonBottomSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  horizontalTripleSplitError f G.outer.1 G.outer.2.lo (ribbonOuterDomains f G hd).bottom
    G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi
def ribbonTopSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  horizontalTripleSplitError f G.outer.1 G.outer.2.hi (ribbonOuterDomains f G hd).top
    G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi
def ribbonLeftSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  verticalTripleSplitError f G.outer.2 G.inner.1.lo (ribbonLeftDomains f G hd).right
    G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi
def ribbonRightSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  verticalTripleSplitError f G.outer.2 G.inner.1.hi (ribbonRightDomains f G hd).left
    G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi

def ribbonSplitCorrection (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) (n : Nat) : Scalar :=
  gridScalarSub (gridScalarSub (ribbonBottomSplit f G hd n) (ribbonTopSplit f G hd n))
    (gridScalarSub (ribbonLeftSplit f G hd n) (ribbonRightSplit f G hd n))

theorem ribbonValueAssembly (ob ot vol vor ib it vil vir lb lt rb rt mb mt lf rf lvb lvt rvb rvt : ScalarAlgebra.Value) :
    ((ob-ot)+(vor-vol))-((ib-it)+(vir-vil)) =
      ((((lb-lt)+(lf-vol))+((rb-rt)+(vor-rf)))+
        (((mb-ib)+(rvb-lvb))+((it-mt)+(rvt-lvt))))+
      (((ob-(lb+(mb+rb)))-(ot-(lt+(mt+rt))))-
        ((lf-(lvb+(vil+lvt)))-(rf-(rvb+(vir+rvt))))) := by
  grind only

theorem ribbonDifference_assembly (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) (n : Nat) :
    ribbonDifference f G hd n ≈ scalarSum (ribbonTileSum f G hd n) (ribbonSplitCorrection f G hd n) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (ribbonDifference f G hd n).property)
    (hright := (scalarSum (ribbonTileSum f G hd n) (ribbonSplitCorrection f G hd n)).property)
  change gridScalarValue (ribbonDifference f G hd n)=
    gridScalarValue (scalarSum (ribbonTileSum f G hd n) (ribbonSplitCorrection f G hd n))
  simp only [ribbonDifference,ribbonOuterBoundary,ribbonInnerBoundary,ribbonTileSum,
    ribbonLeftBoundary,ribbonRightBoundary,ribbonBottomBoundary,ribbonTopBoundary,
    ribbonSplitCorrection,ribbonBottomSplit,ribbonTopSplit,ribbonLeftSplit,ribbonRightSplit,
    continuousRectangleBoundary,rectangleEdgeBoundary,horizontalTripleSplitError,verticalTripleSplitError,
    gridScalarValue_add,gridScalarValue_sub,ribbonLeft,ribbonRight,ribbonBottom,ribbonTop,
    splitIntervalLeft,splitIntervalRight]
  exact ribbonValueAssembly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _


theorem ribbonSplitCorrection_eventual_zero (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (G : RectangleRibbon) (hd : Domains f G) (eps : QPos) :
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

end ComputableAnalysis.RiemannHilbert.BoundaryRibbon
