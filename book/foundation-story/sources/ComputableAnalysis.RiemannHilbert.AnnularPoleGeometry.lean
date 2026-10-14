import ComputableAnalysis.RiemannHilbert.BoundaryHorizontalRibbon

/-! Every represented point in the open rectangular annulus lies strictly
inside one primary tile of the two complementary decompositions. Rational
clearances are derived from interval validity and genuine domain membership;
points on internal cuts are included. Pole-free tile kernel domains are proved. -/
namespace ComputableAnalysis.RiemannHilbert.AnnularPoleGeometry
open ComplexRaw FunctionTheory DomainFunctions RectangularContour
set_option autoImplicit false

def Interior (G : RectangleRibbon) (b : Scalar) : Prop :=
  RectanglePoleInterior G.outer b ∧ ¬representedRectangleContains G.inner b

theorem interior_congr (G : RectangleRibbon) (b c : Scalar) (he : b≈c) (hb : Interior G b) : Interior G c :=
  ⟨rectanglePoleInterior_congr G.outer b c he hb.1,
    fun hc => hb.2 (representedRectangle_congr G.inner c b (equiv_symm he) hc)⟩

theorem strict_upper (x : RealRaw) (hx : x.Valid) (c : Rat) (h : ¬(RealRaw.ofRat c).Le x) :
    ∃ D : QPos, x.Le (RealRaw.ofRat (c-D.val)) := by
  classical
  have hex : ∃ m, (x.compute m).hi<c := by
    apply Classical.byContradiction
    intro hn
    apply h
    intro n m
    by_cases hm : c≤(x.compute m).hi
    · exact hm
    · exact False.elim (hn ⟨m,by grind only⟩)
  obtain ⟨m,hm⟩ := hex
  let D : QPos := ⟨(c-(x.compute m).hi)/2,by rw [Rat.div_def]; exact Rat.mul_pos (by grind only) (by decide +kernel)⟩
  refine ⟨D,?_⟩
  intro n j
  have hv := RealRaw.le_refl x hx n m
  change (x.compute n).lo≤c-D.val
  dsimp [D]
  grind only

theorem strict_lower (x : RealRaw) (hx : x.Valid) (c : Rat) (h : ¬x.Le (RealRaw.ofRat c)) :
    ∃ D : QPos, (RealRaw.ofRat (c+D.val)).Le x := by
  classical
  have hex : ∃ n, c<(x.compute n).lo := by
    apply Classical.byContradiction
    intro hn
    apply h
    intro n m
    by_cases hm : (x.compute n).lo≤c
    · exact hm
    · exact False.elim (hn ⟨n,by grind only⟩)
  obtain ⟨n,hn⟩ := hex
  let D : QPos := ⟨((x.compute n).lo-c)/2,by rw [Rat.div_def]; exact Rat.mul_pos (by grind only) (by decide +kernel)⟩
  refine ⟨D,?_⟩
  intro i m
  have hv := RealRaw.le_refl x hx n m
  change c+D.val≤(x.compute m).hi
  dsimp [D]
  grind only

theorem left_interior (J : QInterval × QInterval) (b : Scalar) (hb : RectanglePoleInterior J b)
    (c : Rat) (D : QPos) (hu : b.val.realPart.Le (RealRaw.ofRat (c-D.val))) :
    RectanglePoleInterior (⟨J.1.lo,c⟩,J.2) b := by
  obtain ⟨H,hh⟩ := hb
  let R := minRadius H D
  have hrH := minRadius_left H D
  have hrD := minRadius_right H D
  refine ⟨R,?_⟩
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · have h := hh.1 n m; change J.1.lo+H.val≤(b.val.compute m).hi.re at h
    change J.1.lo+R.val≤(b.val.compute m).hi.re; grind only
  · have h := hu n m; change (b.val.compute n).lo.re≤c-D.val at h
    change (b.val.compute n).lo.re≤c-R.val; grind only
  · have h := hh.2.2.1 n m; change J.2.lo+H.val≤(b.val.compute m).hi.im at h
    change J.2.lo+R.val≤(b.val.compute m).hi.im; grind only
  · have h := hh.2.2.2 n m; change (b.val.compute n).lo.im≤J.2.hi-H.val at h
    change (b.val.compute n).lo.im≤J.2.hi-R.val; grind only

theorem right_interior (J : QInterval × QInterval) (b : Scalar) (hb : RectanglePoleInterior J b)
    (c : Rat) (D : QPos) (hl : (RealRaw.ofRat (c+D.val)).Le b.val.realPart) :
    RectanglePoleInterior (⟨c,J.1.hi⟩,J.2) b := by
  obtain ⟨H,hh⟩ := hb
  let R := minRadius H D
  have hrH := minRadius_left H D
  have hrD := minRadius_right H D
  refine ⟨R,?_⟩
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · have h := hl n m; change c+D.val≤(b.val.compute m).hi.re at h
    change c+R.val≤(b.val.compute m).hi.re; grind only
  · have h := hh.2.1 n m; change (b.val.compute n).lo.re≤J.1.hi-H.val at h
    change (b.val.compute n).lo.re≤J.1.hi-R.val; grind only
  · have h := hh.2.2.1 n m; change J.2.lo+H.val≤(b.val.compute m).hi.im at h
    change J.2.lo+R.val≤(b.val.compute m).hi.im; grind only
  · have h := hh.2.2.2 n m; change (b.val.compute n).lo.im≤J.2.hi-H.val at h
    change (b.val.compute n).lo.im≤J.2.hi-R.val; grind only

theorem bottom_interior (J : QInterval × QInterval) (b : Scalar) (hb : RectanglePoleInterior J b)
    (c : Rat) (D : QPos) (hu : b.val.imagPart.Le (RealRaw.ofRat (c-D.val))) :
    RectanglePoleInterior (J.1,⟨J.2.lo,c⟩) b := by
  obtain ⟨H,hh⟩ := hb
  let R := minRadius H D
  have hrH := minRadius_left H D
  have hrD := minRadius_right H D
  refine ⟨R,?_⟩
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · have h := hh.1 n m; change J.1.lo+H.val≤(b.val.compute m).hi.re at h
    change J.1.lo+R.val≤(b.val.compute m).hi.re; grind only
  · have h := hh.2.1 n m; change (b.val.compute n).lo.re≤J.1.hi-H.val at h
    change (b.val.compute n).lo.re≤J.1.hi-R.val; grind only
  · have h := hh.2.2.1 n m; change J.2.lo+H.val≤(b.val.compute m).hi.im at h
    change J.2.lo+R.val≤(b.val.compute m).hi.im; grind only
  · have h := hu n m; change (b.val.compute n).lo.im≤c-D.val at h
    change (b.val.compute n).lo.im≤c-R.val; grind only

theorem top_interior (J : QInterval × QInterval) (b : Scalar) (hb : RectanglePoleInterior J b)
    (c : Rat) (D : QPos) (hl : (RealRaw.ofRat (c+D.val)).Le b.val.imagPart) :
    RectanglePoleInterior (J.1,⟨c,J.2.hi⟩) b := by
  obtain ⟨H,hh⟩ := hb
  let R := minRadius H D
  have hrH := minRadius_left H D
  have hrD := minRadius_right H D
  refine ⟨R,?_⟩
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · have h := hh.1 n m; change J.1.lo+H.val≤(b.val.compute m).hi.re at h
    change J.1.lo+R.val≤(b.val.compute m).hi.re; grind only
  · have h := hh.2.1 n m; change (b.val.compute n).lo.re≤J.1.hi-H.val at h
    change (b.val.compute n).lo.re≤J.1.hi-R.val; grind only
  · have h := hl n m; change c+D.val≤(b.val.compute m).hi.im at h
    change c+R.val≤(b.val.compute m).hi.im; grind only
  · have h := hh.2.2.2 n m; change (b.val.compute n).lo.im≤J.2.hi-H.val at h
    change (b.val.compute n).lo.im≤J.2.hi-R.val; grind only

theorem locate (G : RectangleRibbon) (b : Scalar) (hb : Interior G b) :
    RectanglePoleInterior (ribbonLeft G) b ∨ RectanglePoleInterior (ribbonRight G) b ∨
      RectanglePoleInterior (BoundaryHorizontalRibbon.bottomRectangle G) b ∨
        RectanglePoleInterior (BoundaryHorizontalRibbon.topRectangle G) b := by
  classical
  by_cases hxl : (RealRaw.ofRat G.inner.1.lo).Le b.val.realPart
  · by_cases hxr : b.val.realPart.Le (RealRaw.ofRat G.inner.1.hi)
    · by_cases hyl : (RealRaw.ofRat G.inner.2.lo).Le b.val.imagPart
      · by_cases hyr : b.val.imagPart.Le (RealRaw.ofRat G.inner.2.hi)
        · exact False.elim (hb.2 ⟨hxl,hxr,hyl,hyr⟩)
        · obtain ⟨D,hD⟩ := strict_lower _ (imagPart_valid b.property) _ hyr
          exact Or.inr (Or.inr (Or.inr (top_interior G.outer b hb.1 _ D hD)))
      · obtain ⟨D,hD⟩ := strict_upper _ (imagPart_valid b.property) _ hyl
        exact Or.inr (Or.inr (Or.inl (bottom_interior G.outer b hb.1 _ D hD)))
    · obtain ⟨D,hD⟩ := strict_lower _ (realPart_valid b.property) _ hxr
      exact Or.inr (Or.inl (right_interior G.outer b hb.1 _ D hD))
  · obtain ⟨D,hD⟩ := strict_upper _ (realPart_valid b.property) _ hxl
    exact Or.inl (left_interior G.outer b hb.1 _ D hD)

theorem source_mem (f : DomainFunctions.Map) (G : RectangleRibbon) (hd : RibbonDomain f G)
    (b : Scalar) (hb : Interior G b) : f.domain b := by
  rcases locate G b hb with hL|hR|hB|hT
  · exact ribbon_left_domain f G hd b (rectanglePoleInterior_mem _ b hL)
  · exact ribbon_right_domain f G hd b (rectanglePoleInterior_mem _ b hR)
  · exact BoundaryHorizontalRibbon.bottom_domain f G hd b (rectanglePoleInterior_mem _ b hB)
  · exact BoundaryHorizontalRibbon.top_domain f G hd b (rectanglePoleInterior_mem _ b hT)

theorem excludes (J K : QInterval × QInterval) (b : Scalar) (hb : RectanglePoleInterior J b)
    (hs : J.1.hi≤K.1.lo ∨ K.1.hi≤J.1.lo ∨ J.2.hi≤K.2.lo ∨ K.2.hi≤J.2.lo) :
    ¬representedRectangleContains K b := by
  obtain ⟨D,hD⟩ := hb
  intro hk
  have hp := D.property
  rcases hs with hs|hs|hs|hs
  · have h := (RealRaw.le_trans (realPart_valid b.property) hk.1 hD.2.1) 0 0
    change K.1.lo≤J.1.hi-D.val at h
    grind only
  · have h := (RealRaw.le_trans (realPart_valid b.property) hD.1 hk.2.1) 0 0
    change J.1.lo+D.val≤K.1.hi at h
    grind only
  · have h := (RealRaw.le_trans (imagPart_valid b.property) hk.2.2.1 hD.2.2.2) 0 0
    change K.2.lo≤J.2.hi-D.val at h
    grind only
  · have h := (RealRaw.le_trans (imagPart_valid b.property) hD.2.2.1 hk.2.2.2) 0 0
    change J.2.lo+D.val≤K.2.hi at h
    grind only

theorem offset_nonzero (J : QInterval × QInterval) (b w : Scalar)
    (hb : ¬representedRectangleContains J b) (hw : representedRectangleContains J w) :
    NonzeroBoxSearch.Nonzero ((ribbonPoleOffset b).eval w trivial) := by
  intro he
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((ribbonPoleOffset b).eval w trivial).property) (hright := ofQComplex_valid _) he
  change -gridScalarValue b+1*gridScalarValue w=0 at h
  have hwb : w≈b := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := w.property) (hright := b.property)
    change gridScalarValue w=gridScalarValue b
    grind only
  exact hb (representedRectangle_congr J w b hwb hw)

theorem kernel_domain (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : ∀ w, representedRectangleContains J w → f.domain w) (b : Scalar)
    (hb : ¬representedRectangleContains J b) :
    ∀ w, representedRectangleContains J w → (ribbonCauchyKernel f b).domain w :=
  fun w hw => ⟨hd w hw,⟨trivial,offset_nonzero J b w hb hw⟩⟩

end ComputableAnalysis.RiemannHilbert.AnnularPoleGeometry
