import ComputableAnalysis.RiemannHilbert.BoundaryRibbonAssembly

/-! The complementary horizontal four-tile ribbon decomposition. Boundary
assembly is proved for actual edge values alone. Whole source domains on these
tiles are derived from the original ribbon, without filling its inner hole. -/
namespace ComputableAnalysis.RiemannHilbert.BoundaryHorizontalRibbon
open ComplexRaw FunctionTheory DomainFunctions RectangularContour
set_option autoImplicit false

def leftRectangle (G : RectangleRibbon) : QInterval × QInterval := (⟨G.outer.1.lo,G.inner.1.lo⟩,G.inner.2)
def rightRectangle (G : RectangleRibbon) : QInterval × QInterval := (⟨G.inner.1.hi,G.outer.1.hi⟩,G.inner.2)
def bottomRectangle (G : RectangleRibbon) : QInterval × QInterval := (G.outer.1,⟨G.outer.2.lo,G.inner.2.lo⟩)
def topRectangle (G : RectangleRibbon) : QInterval × QInterval := (G.outer.1,⟨G.inner.2.hi,G.outer.2.hi⟩)

theorem horizontal_three_cover (I J : QInterval) (c d : Rat) (z : Scalar)
    (hz : representedRectangleContains (I,J) z) :
    representedRectangleContains (splitIntervalLeft I c,J) z ∨
      representedRectangleContains (⟨c,d⟩,J) z ∨ representedRectangleContains (splitIntervalRight I d,J) z := by
  rcases represented_rational_cut z.val.realPart (realPart_valid z.property) c with hc|hc
  · exact Or.inl ⟨hz.1,hc,hz.2.2.1,hz.2.2.2⟩
  · rcases represented_rational_cut z.val.realPart (realPart_valid z.property) d with hd|hd
    · exact Or.inr (Or.inl ⟨hc,hd,hz.2.2.1,hz.2.2.2⟩)
    · exact Or.inr (Or.inr ⟨hd,hz.2.1,hz.2.2.1,hz.2.2.2⟩)

theorem vertical_three_cover (I J : QInterval) (c d : Rat) (z : Scalar)
    (hz : representedRectangleContains (I,J) z) :
    representedRectangleContains (I,splitIntervalLeft J c) z ∨
      representedRectangleContains (I,⟨c,d⟩) z ∨ representedRectangleContains (I,splitIntervalRight J d) z := by
  rcases represented_rational_cut z.val.imagPart (imagPart_valid z.property) c with hc|hc
  · exact Or.inl ⟨hz.1,hz.2.1,hz.2.2.1,hc⟩
  · rcases represented_rational_cut z.val.imagPart (imagPart_valid z.property) d with hd|hd
    · exact Or.inr (Or.inl ⟨hz.1,hz.2.1,hc,hd⟩)
    · exact Or.inr (Or.inr ⟨hz.1,hz.2.1,hd,hz.2.2.2⟩)

theorem left_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    ∀ z, representedRectangleContains (leftRectangle G) z → f.domain z :=
  fun z hz => hd z (Or.inl (representedRectangle_subrectangle (ribbonLeft G) (leftRectangle G) z
    Rat.le_refl Rat.le_refl G.yLo G.yHi hz))

theorem right_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    ∀ z, representedRectangleContains (rightRectangle G) z → f.domain z :=
  fun z hz => hd z (Or.inr (Or.inl (representedRectangle_subrectangle (ribbonRight G) (rightRectangle G) z
    Rat.le_refl Rat.le_refl G.yLo G.yHi hz)))

theorem bottom_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    ∀ z, representedRectangleContains (bottomRectangle G) z → f.domain z := by
  intro z hz
  rcases horizontal_three_cover G.outer.1 (bottomRectangle G).2 G.inner.1.lo G.inner.1.hi z hz with hL|hB|hR
  · exact hd z (Or.inl (representedRectangle_subrectangle (ribbonLeft G) (splitIntervalLeft G.outer.1 G.inner.1.lo,(bottomRectangle G).2) z
      Rat.le_refl Rat.le_refl Rat.le_refl (Rat.le_trans G.yOrder G.yHi) hL))
  · exact hd z (Or.inr (Or.inr (Or.inl hB)))
  · exact hd z (Or.inr (Or.inl (representedRectangle_subrectangle (ribbonRight G) (splitIntervalRight G.outer.1 G.inner.1.hi,(bottomRectangle G).2) z
      Rat.le_refl Rat.le_refl Rat.le_refl (Rat.le_trans G.yOrder G.yHi) hR)))

theorem top_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    ∀ z, representedRectangleContains (topRectangle G) z → f.domain z := by
  intro z hz
  rcases horizontal_three_cover G.outer.1 (topRectangle G).2 G.inner.1.lo G.inner.1.hi z hz with hL|hT|hR
  · exact hd z (Or.inl (representedRectangle_subrectangle (ribbonLeft G) (splitIntervalLeft G.outer.1 G.inner.1.lo,(topRectangle G).2) z
      Rat.le_refl Rat.le_refl (Rat.le_trans G.yLo G.yOrder) Rat.le_refl hL))
  · exact hd z (Or.inr (Or.inr (Or.inr hT)))
  · exact hd z (Or.inr (Or.inl (representedRectangle_subrectangle (ribbonRight G) (splitIntervalRight G.outer.1 G.inner.1.hi,(topRectangle G).2) z
      Rat.le_refl Rat.le_refl (Rat.le_trans G.yLo G.yOrder) Rat.le_refl hR)))

structure Domains (f : DomainFunctions.Map) (G : RectangleRibbon) : Prop where
  left : RectangleBoundaryDomains f (leftRectangle G)
  right : RectangleBoundaryDomains f (rightRectangle G)
  bottom : RectangleBoundaryDomains f (bottomRectangle G)
  top : RectangleBoundaryDomains f (topRectangle G)

theorem outerDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) :
    RectangleBoundaryDomains f G.outer := {
  bottom := hd.bottom.bottom
  top := hd.top.top
  left z hz := by
    rcases vertical_three_cover (⟨G.outer.1.lo,G.outer.1.lo⟩ : QInterval) G.outer.2 G.inner.2.lo G.inner.2.hi z hz with hB|hL|hT
    · exact hd.bottom.left z hB
    · exact hd.left.left z hL
    · exact hd.top.left z hT
  right z hz := by
    rcases vertical_three_cover (⟨G.outer.1.hi,G.outer.1.hi⟩ : QInterval) G.outer.2 G.inner.2.lo G.inner.2.hi z hz with hB|hR|hT
    · exact hd.bottom.right z hB
    · exact hd.right.right z hR
    · exact hd.top.right z hT
}

theorem innerDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) :
    RectangleBoundaryDomains f G.inner := {
  bottom := horizontalInterval_subdomain f G.outer.1 G.inner.1 G.inner.2.lo hd.bottom.top G.xLo G.xHi
  top := horizontalInterval_subdomain f G.outer.1 G.inner.1 G.inner.2.hi hd.top.bottom G.xLo G.xHi
  left := hd.left.right
  right := hd.right.left
}

def outerBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f G.outer (outerDomains f G hd)
def innerBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f G.inner (innerDomains f G hd)
def leftBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f (leftRectangle G) hd.left
def rightBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f (rightRectangle G) hd.right
def bottomBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f (bottomRectangle G) hd.bottom
def topBoundary (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  continuousRectangleBoundary f (topRectangle G) hd.top

def tileSum (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) (n : Nat) : Scalar :=
  scalarSum (scalarSum (bottomBoundary f G hd n) (topBoundary f G hd n))
    (scalarSum (leftBoundary f G hd n) (rightBoundary f G hd n))
def difference (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) (n : Nat) : Scalar :=
  gridScalarSub (outerBoundary f G hd n) (innerBoundary f G hd n)

def bottomSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  horizontalTripleSplitError f G.outer.1 G.inner.2.lo hd.bottom.top
    G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi
def topSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  horizontalTripleSplitError f G.outer.1 G.inner.2.hi hd.top.bottom
    G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi
def leftSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  verticalTripleSplitError f G.outer.2 G.outer.1.lo (outerDomains f G hd).left
    G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi
def rightSplit (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) : Nat → Scalar :=
  verticalTripleSplitError f G.outer.2 G.outer.1.hi (outerDomains f G hd).right
    G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi
def correction (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) (n : Nat) : Scalar :=
  scalarSum (gridScalarSub (bottomSplit f G hd n) (topSplit f G hd n))
    (gridScalarSub (rightSplit f G hd n) (leftSplit f G hd n))

theorem valueAssembly (ob ot vl vr ib it il ir wb wt vbl vbr vtl vtr lb lt rb rt vml vmr : ScalarAlgebra.Value) :
    ((ob-ot)+(vr-vl))-((ib-it)+(ir-il))=
      ((((ob-wb)+(vbr-vbl))+((wt-ot)+(vtr-vtl)))+
        (((lb-lt)+(il-vml))+((rb-rt)+(vmr-ir))))+
      (((wb-(lb+(ib+rb)))-(wt-(lt+(it+rt))))+
        ((vr-(vbr+(vmr+vtr)))-(vl-(vbl+(vml+vtl))))) := by grind only

theorem assembly (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : Domains f G) (n : Nat) :
    difference f G hd n≈scalarSum (tileSum f G hd n) (correction f G hd n) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (difference f G hd n).property)
    (hright := (scalarSum (tileSum f G hd n) (correction f G hd n)).property)
  change gridScalarValue (difference f G hd n)=gridScalarValue (scalarSum (tileSum f G hd n) (correction f G hd n))
  simp only [difference,outerBoundary,innerBoundary,tileSum,leftBoundary,rightBoundary,bottomBoundary,topBoundary,
    correction,bottomSplit,topSplit,leftSplit,rightSplit,continuousRectangleBoundary,rectangleEdgeBoundary,
    horizontalTripleSplitError,verticalTripleSplitError,gridScalarValue_add,gridScalarValue_sub,
    leftRectangle,rightRectangle,bottomRectangle,topRectangle,splitIntervalLeft,splitIntervalRight]
  exact valueAssembly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem correction_eventual_zero (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (G : RectangleRibbon) (hd : Domains f G) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (correction f G hd n).val eps.val := by
  let eta := divideRadius eps (⟨4,by decide +kernel⟩ : QPos)
  obtain ⟨B,hB⟩ := horizontalTripleSplitError_eventual_zero f hc G.outer.1 G.inner.2.lo hd.bottom.top
    G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi eta
  obtain ⟨T,hT⟩ := horizontalTripleSplitError_eventual_zero f hc G.outer.1 G.inner.2.hi hd.top.bottom
    G.inner.1.lo G.inner.1.hi G.xLo G.xOrder G.xHi eta
  obtain ⟨L,hL⟩ := verticalTripleSplitError_eventual_zero f hc G.outer.2 G.outer.1.lo (outerDomains f G hd).left
    G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi eta
  obtain ⟨R,hR⟩ := verticalTripleSplitError_eventual_zero f hc G.outer.2 G.outer.1.hi (outerDomains f G hd).right
    G.inner.2.lo G.inner.2.hi G.yLo G.yOrder G.yHi eta
  refine ⟨max (max B T) (max L R),?_⟩
  intro n hn
  have hs := LocalODE.small_add (SeriesLimitLaws.small_sub (hB n (by omega)) (hT n (by omega)))
    (SeriesLimitLaws.small_sub (hR n (by omega)) (hL n (by omega)))
  have he : (eta.val+eta.val)+(eta.val+eta.val)=eps.val := by
    have h := divideRadius_identity eps (⟨4,by decide +kernel⟩ : QPos)
    change 4*eta.val=eps.val at h
    grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.RiemannHilbert.BoundaryHorizontalRibbon
