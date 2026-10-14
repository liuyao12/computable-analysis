import ComputableAnalysis.RiemannHilbert.ContourBoundarySampler

/-! Pointwise continuity proves rational sample boundedness on certified
edges. The finite-cover bound remains existential in Prop. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem rationalRectangle_bisect_cover (J : QInterval × QInterval) (q : QComplex)
    (hq : rationalRectangleContains J q) :
    rationalRectangleContains (bisectRectangle J (false,false)) q ∨
    rationalRectangleContains (bisectRectangle J (false,true)) q ∨
    rationalRectangleContains (bisectRectangle J (true,false)) q ∨
    rationalRectangleContains (bisectRectangle J (true,true)) q := by
  by_cases hx : q.re≤J.1.midpoint <;> by_cases hy : q.im≤J.2.midpoint
  · exact Or.inl ⟨hq.1,hx,hq.2.2.1,hy⟩
  · exact Or.inr (Or.inl ⟨hq.1,hx,(show J.2.midpoint≤q.im by grind only),hq.2.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(show J.1.midpoint≤q.re by grind only),hq.2.1,hq.2.2.1,hy⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨(show J.1.midpoint≤q.re by grind only),hq.2.1,
      (show J.2.midpoint≤q.im by grind only),hq.2.2.2⟩))

theorem valueRectangleCover_rational_bound (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (J : QInterval × QInterval) (cover : DomainValueRectangleCover f hc unitError J) :
    ∃ B : Rat, 0≤B ∧ ∀ q, rationalRectangleContains J q →
      ∀ hz, Small (f.eval (rationalRectangleScalar q) hz).val B := by
  induction cover with
  | neighborhood J a ha hnear =>
    refine ⟨scalarBound (f.eval a ha)+1,by have h := scalarBound_pos (f.eval a ha); grind only,?_⟩
    intro q hq hz
    have h := hc.estimate a ha unitError _ hz (hnear q hq)
    have hs := LocalODE.small_add (scalar_small (f.eval a ha)) h
    exact Small.congr (add_valid (f.eval a ha).property
      (sub_valid (f.eval _ hz).property (f.eval a ha).property)) (f.eval _ hz).property
      (SeriesLimitLaws.add_difference _ _ (f.eval _ hz).property (f.eval a ha).property) hs
  | split J ll lr rl rr ill ilr irl irr =>
    obtain ⟨L,hL,bL⟩ := ill
    obtain ⟨T,hT,bT⟩ := ilr
    obtain ⟨R,hR,bR⟩ := irl
    obtain ⟨U,hU,bU⟩ := irr
    refine ⟨(L+T)+(R+U),Rat.add_nonneg (Rat.add_nonneg hL hT) (Rat.add_nonneg hR hU),?_⟩
    intro q hq hz
    rcases rationalRectangle_bisect_cover J q hq with hq|hq|hq|hq
    · exact (bL q hq hz).mono (by grind only)
    · exact (bT q hq hz).mono (by grind only)
    · exact (bR q hq hz).mono (by grind only)
    · exact (bU q hq hz).mono (by grind only)

theorem continuousRectangle_rational_bound (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : ∀ z, representedRectangleContains J z → f.domain z) :
    ∃ B : Rat, 0≤B ∧ ∀ q, rationalRectangleContains J q →
      ∀ hz, Small (f.eval (rationalRectangleScalar q) hz).val B :=
  valueRectangleCover_rational_bound f hc J (domain_value_rectangle_cover f hc unitError J hX hY hd)

theorem continuousRectangleBoundary_rational_bound (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (J : QInterval × QInterval) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hd : RectangleBoundaryDomains f J) :
    ∃ B : Rat, 0≤B ∧ ∀ q, rationalRectangleBoundaryContains J q →
      ∀ hz, Small (f.eval (rationalRectangleScalar q) hz).val B := by
  obtain ⟨B,hB,bB⟩ := continuousRectangle_rational_bound f hc (horizontalIntervalRectangle J.1 J.2.lo) hX Rat.le_refl hd.bottom
  obtain ⟨T,hT,bT⟩ := continuousRectangle_rational_bound f hc (horizontalIntervalRectangle J.1 J.2.hi) hX Rat.le_refl hd.top
  obtain ⟨L,hL,bL⟩ := continuousRectangle_rational_bound f hc (verticalIntervalRectangle J.2 J.1.lo) Rat.le_refl hY hd.left
  obtain ⟨R,hR,bR⟩ := continuousRectangle_rational_bound f hc (verticalIntervalRectangle J.2 J.1.hi) Rat.le_refl hY hd.right
  refine ⟨(B+T)+(L+R),Rat.add_nonneg (Rat.add_nonneg hB hT) (Rat.add_nonneg hL hR),?_⟩
  intro q hq hz
  rcases hq with hq|hq|hq|hq
  · exact (bB q hq hz).mono (by grind only)
  · exact (bT q hq hz).mono (by grind only)
  · exact (bL q hq hz).mono (by grind only)
  · exact (bR q hq hz).mono (by grind only)

end ComputableAnalysis.RiemannHilbert.RectangularContour
