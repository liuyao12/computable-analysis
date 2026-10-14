import ComputableAnalysis.RiemannHilbert.ContourBoundaryEdges
import ComputableAnalysis.RiemannHilbert.ContourTripleSplit

/-! Four rational rectangles cover the ribbon between nested rectangles.
All represented boundary domains are derived from the actual ribbon domain. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

structure RectangleRibbon where
  outer : QInterval × QInterval
  inner : QInterval × QInterval
  xLo : outer.1.lo≤inner.1.lo
  xOrder : inner.1.lo≤inner.1.hi
  xHi : inner.1.hi≤outer.1.hi
  yLo : outer.2.lo≤inner.2.lo
  yOrder : inner.2.lo≤inner.2.hi
  yHi : inner.2.hi≤outer.2.hi

def ribbonLeft (G : RectangleRibbon) : QInterval × QInterval := (⟨G.outer.1.lo,G.inner.1.lo⟩,G.outer.2)
def ribbonRight (G : RectangleRibbon) : QInterval × QInterval := (⟨G.inner.1.hi,G.outer.1.hi⟩,G.outer.2)
def ribbonBottom (G : RectangleRibbon) : QInterval × QInterval := (G.inner.1,⟨G.outer.2.lo,G.inner.2.lo⟩)
def ribbonTop (G : RectangleRibbon) : QInterval × QInterval := (G.inner.1,⟨G.inner.2.hi,G.outer.2.hi⟩)

def ribbonContains (G : RectangleRibbon) (z : Scalar) : Prop :=
  representedRectangleContains (ribbonLeft G) z ∨ representedRectangleContains (ribbonRight G) z ∨
    representedRectangleContains (ribbonBottom G) z ∨ representedRectangleContains (ribbonTop G) z

def RibbonDomain (f : DomainFunctions.Map) (G : RectangleRibbon) : Prop :=
  ∀ z : Scalar, ribbonContains G z → f.domain z

theorem ribbon_outer_x_order (G : RectangleRibbon) : G.outer.1.lo≤G.outer.1.hi :=
  Rat.le_trans G.xLo (Rat.le_trans G.xOrder G.xHi)
theorem ribbon_outer_y_order (G : RectangleRibbon) : G.outer.2.lo≤G.outer.2.hi :=
  Rat.le_trans G.yLo (Rat.le_trans G.yOrder G.yHi)

theorem represented_rational_cut (x : RealRaw) (hx : x.Valid) (c : Rat) :
    x.Le (RealRaw.ofRat c) ∨ (RealRaw.ofRat c).Le x := by
  classical
  by_cases h : x.Le (RealRaw.ofRat c)
  · exact Or.inl h
  · right
    intro n m
    by_cases hm : c≤(x.compute m).hi
    · exact hm
    · exfalso
      apply h
      intro j k
      have hjm := RealRaw.le_refl x hx j m
      change (x.compute j).lo≤c
      grind only

theorem representedHorizontal_three_cover (I : QInterval) (y c d : Rat) (z : Scalar)
    (hz : representedRectangleContains (horizontalIntervalRectangle I y) z) :
    representedRectangleContains (horizontalIntervalRectangle (splitIntervalLeft I c) y) z ∨
    representedRectangleContains (horizontalIntervalRectangle ⟨c,d⟩ y) z ∨
    representedRectangleContains (horizontalIntervalRectangle (splitIntervalRight I d) y) z := by
  rcases represented_rational_cut z.val.realPart (realPart_valid z.property) c with hc | hc
  · exact Or.inl ⟨hz.1,hc,hz.2.2.1,hz.2.2.2⟩
  · rcases represented_rational_cut z.val.realPart (realPart_valid z.property) d with hd | hd
    · exact Or.inr (Or.inl ⟨hc,hd,hz.2.2.1,hz.2.2.2⟩)
    · exact Or.inr (Or.inr ⟨hd,hz.2.1,hz.2.2.1,hz.2.2.2⟩)

theorem ribbon_left_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    ∀ z : Scalar, representedRectangleContains (ribbonLeft G) z → f.domain z :=
  fun z hz => hd z (Or.inl hz)
theorem ribbon_right_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    ∀ z : Scalar, representedRectangleContains (ribbonRight G) z → f.domain z :=
  fun z hz => hd z (Or.inr (Or.inl hz))
theorem ribbon_bottom_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    ∀ z : Scalar, representedRectangleContains (ribbonBottom G) z → f.domain z :=
  fun z hz => hd z (Or.inr (Or.inr (Or.inl hz)))
theorem ribbon_top_domain (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    ∀ z : Scalar, representedRectangleContains (ribbonTop G) z → f.domain z :=
  fun z hz => hd z (Or.inr (Or.inr (Or.inr hz)))

theorem ribbon_outer_bottom_contains (G : RectangleRibbon) (z : Scalar)
    (hz : representedRectangleContains (horizontalIntervalRectangle G.outer.1 G.outer.2.lo) z) : ribbonContains G z := by
  rcases representedHorizontal_three_cover G.outer.1 G.outer.2.lo G.inner.1.lo G.inner.1.hi z hz with hL | hM | hR
  · exact Or.inl (representedRectangle_subrectangle (ribbonLeft G)
      (horizontalIntervalRectangle (splitIntervalLeft G.outer.1 G.inner.1.lo) G.outer.2.lo) z
      Rat.le_refl Rat.le_refl Rat.le_refl (ribbon_outer_y_order G) hL)
  · exact Or.inr (Or.inr (Or.inl (representedRectangle_subrectangle (ribbonBottom G)
      (horizontalIntervalRectangle G.inner.1 G.outer.2.lo) z
      Rat.le_refl Rat.le_refl Rat.le_refl G.yLo hM)))
  · exact Or.inr (Or.inl (representedRectangle_subrectangle (ribbonRight G)
      (horizontalIntervalRectangle (splitIntervalRight G.outer.1 G.inner.1.hi) G.outer.2.lo) z
      Rat.le_refl Rat.le_refl Rat.le_refl (ribbon_outer_y_order G) hR))

theorem ribbon_outer_top_contains (G : RectangleRibbon) (z : Scalar)
    (hz : representedRectangleContains (horizontalIntervalRectangle G.outer.1 G.outer.2.hi) z) : ribbonContains G z := by
  rcases representedHorizontal_three_cover G.outer.1 G.outer.2.hi G.inner.1.lo G.inner.1.hi z hz with hL | hM | hR
  · exact Or.inl (representedRectangle_subrectangle (ribbonLeft G)
      (horizontalIntervalRectangle (splitIntervalLeft G.outer.1 G.inner.1.lo) G.outer.2.hi) z
      Rat.le_refl Rat.le_refl (ribbon_outer_y_order G) Rat.le_refl hL)
  · exact Or.inr (Or.inr (Or.inr (representedRectangle_subrectangle (ribbonTop G)
      (horizontalIntervalRectangle G.inner.1 G.outer.2.hi) z
      Rat.le_refl Rat.le_refl G.yHi Rat.le_refl hM)))
  · exact Or.inr (Or.inl (representedRectangle_subrectangle (ribbonRight G)
      (horizontalIntervalRectangle (splitIntervalRight G.outer.1 G.inner.1.hi) G.outer.2.hi) z
      Rat.le_refl Rat.le_refl (ribbon_outer_y_order G) Rat.le_refl hR))

def ribbonOuterDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    RectangleBoundaryDomains f G.outer where
  bottom := fun z hz => hd z (ribbon_outer_bottom_contains G z hz)
  top := fun z hz => hd z (ribbon_outer_top_contains G z hz)
  left := (rectangleBoundaryDomains_of_rectangle f (ribbonLeft G) G.xLo (ribbon_outer_y_order G)
    (ribbon_left_domain f G hd)).left
  right := (rectangleBoundaryDomains_of_rectangle f (ribbonRight G) G.xHi (ribbon_outer_y_order G)
    (ribbon_right_domain f G hd)).right

def ribbonInnerDomains (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G) :
    RectangleBoundaryDomains f G.inner where
  bottom := (rectangleBoundaryDomains_of_rectangle f (ribbonBottom G) G.xOrder G.yLo
    (ribbon_bottom_domain f G hd)).top
  top := (rectangleBoundaryDomains_of_rectangle f (ribbonTop G) G.xOrder G.yHi
    (ribbon_top_domain f G hd)).bottom
  left := verticalInterval_subdomain f G.outer.2 G.inner.2 G.inner.1.lo
    (rectangleBoundaryDomains_of_rectangle f (ribbonLeft G) G.xLo (ribbon_outer_y_order G)
      (ribbon_left_domain f G hd)).right G.yLo G.yHi
  right := verticalInterval_subdomain f G.outer.2 G.inner.2 G.inner.1.hi
    (rectangleBoundaryDomains_of_rectangle f (ribbonRight G) G.xHi (ribbon_outer_y_order G)
      (ribbon_right_domain f G hd)).left G.yLo G.yHi

theorem ribbonContains_outer (G : RectangleRibbon) (z : Scalar) (hz : ribbonContains G z) :
    representedRectangleContains G.outer z := by
  rcases hz with hL | hR | hB | hT
  · exact representedRectangle_subrectangle G.outer (ribbonLeft G) z
      Rat.le_refl (Rat.le_trans G.xOrder G.xHi) Rat.le_refl Rat.le_refl hL
  · exact representedRectangle_subrectangle G.outer (ribbonRight G) z
      (Rat.le_trans G.xLo G.xOrder) Rat.le_refl Rat.le_refl Rat.le_refl hR
  · exact representedRectangle_subrectangle G.outer (ribbonBottom G) z
      G.xLo G.xHi Rat.le_refl (Rat.le_trans G.yOrder G.yHi) hB
  · exact representedRectangle_subrectangle G.outer (ribbonTop G) z
      G.xLo G.xHi (Rat.le_trans G.yLo G.yOrder) Rat.le_refl hT

theorem ribbonDomain_of_outer (f : DomainFunctions.Map) (G : RectangleRibbon)
    (hd : ∀ z : Scalar, representedRectangleContains G.outer z → f.domain z) : RibbonDomain f G :=
  fun z hz => hd z (ribbonContains_outer G z hz)

end ComputableAnalysis.RiemannHilbert.RectangularContour
