import ComputableAnalysis.RiemannHilbert.ContourRibbonGeometry

/-! The four actual ribbon boundaries cancel, up to four actual split
errors. This is exact finite represented algebra before any limit argument. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def ribbonLeftDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    RectangleBoundaryDomains f (ribbonLeft G) :=
  rectangleBoundaryDomains_of_rectangle f _ G.xLo (ribbon_outer_y_order G) (ribbon_left_domain f G hd)
def ribbonRightDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    RectangleBoundaryDomains f (ribbonRight G) :=
  rectangleBoundaryDomains_of_rectangle f _ G.xHi (ribbon_outer_y_order G) (ribbon_right_domain f G hd)
def ribbonBottomDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    RectangleBoundaryDomains f (ribbonBottom G) :=
  rectangleBoundaryDomains_of_rectangle f _ G.xOrder G.yLo (ribbon_bottom_domain f G hd)
def ribbonTopDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    RectangleBoundaryDomains f (ribbonTop G) :=
  rectangleBoundaryDomains_of_rectangle f _ G.xOrder G.yHi (ribbon_top_domain f G hd)

def ribbonOuterBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  continuousRectangleBoundary f G.outer (ribbonOuterDomains f G hd)
def ribbonInnerBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  continuousRectangleBoundary f G.inner (ribbonInnerDomains f G hd)
def ribbonLeftBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  continuousRectangleBoundary f (ribbonLeft G) (ribbonLeftDomains f G hd)
def ribbonRightBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  continuousRectangleBoundary f (ribbonRight G) (ribbonRightDomains f G hd)
def ribbonBottomBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  continuousRectangleBoundary f (ribbonBottom G) (ribbonBottomDomains f G hd)
def ribbonTopBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  continuousRectangleBoundary f (ribbonTop G) (ribbonTopDomains f G hd)

def ribbonTileSum (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) (n : Nat) : Scalar :=
  scalarSum (scalarSum (ribbonLeftBoundary f G hd n) (ribbonRightBoundary f G hd n))
    (scalarSum (ribbonBottomBoundary f G hd n) (ribbonTopBoundary f G hd n))
def ribbonDifference (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) (n : Nat) : Scalar :=
  gridScalarSub (ribbonOuterBoundary f G hd n) (ribbonInnerBoundary f G hd n)

def ribbonBottomSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  horizontalTripleSplitError f G.outer.1 G.outer.2.lo (ribbonOuterDomains f G hd).bottom
    G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi
def ribbonTopSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  horizontalTripleSplitError f G.outer.1 G.outer.2.hi (ribbonOuterDomains f G hd).top
    G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi
def ribbonLeftSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  verticalTripleSplitError f G.outer.2 G.inner.1.lo (ribbonLeftDomains f G hd).right
    G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi
def ribbonRightSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) : Nat → Scalar :=
  verticalTripleSplitError f G.outer.2 G.inner.1.hi (ribbonRightDomains f G hd).left
    G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi

def ribbonSplitCorrection (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) (n : Nat) : Scalar :=
  gridScalarSub (gridScalarSub (ribbonBottomSplit f G hd n) (ribbonTopSplit f G hd n))
    (gridScalarSub (ribbonLeftSplit f G hd n) (ribbonRightSplit f G hd n))

theorem ribbonValueAssembly (ob ot vol vor ib it vil vir lb lt rb rt mb mt lf rf lvb lvt rvb rvt : ScalarAlgebra.Value) :
    ((ob-ot)+(vor-vol))-((ib-it)+(vir-vil)) =
      ((((lb-lt)+(lf-vol))+((rb-rt)+(vor-rf)))+
        (((mb-ib)+(rvb-lvb))+((it-mt)+(rvt-lvt))))+
      (((ob-(lb+(mb+rb)))-(ot-(lt+(mt+rt))))-
        ((lf-(lvb+(vil+lvt)))-(rf-(rvb+(vir+rvt))))) := by
  grind only

theorem ribbonDifference_assembly (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) (n : Nat) :
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

end ComputableAnalysis.RiemannHilbert.RectangularContour
