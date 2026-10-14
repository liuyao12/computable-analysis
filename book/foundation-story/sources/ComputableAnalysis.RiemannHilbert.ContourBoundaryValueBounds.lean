import ComputableAnalysis.RiemannHilbert.ContourRectangleApproximation

/-! Actual value bounds on the four represented edges. Rational sample
evidence is extended by pointwise continuity and rational approximation. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

structure RectangleBoundaryValueBound (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hd : RectangleBoundaryDomains f J) (B : QPos) : Prop where
  bottom : ∀ z (hz : representedRectangleContains (horizontalIntervalRectangle J.1 J.2.lo) z),
    Small (f.eval z (hd.bottom z hz)).val B.val
  top : ∀ z (hz : representedRectangleContains (horizontalIntervalRectangle J.1 J.2.hi) z),
    Small (f.eval z (hd.top z hz)).val B.val
  left : ∀ z (hz : representedRectangleContains (verticalIntervalRectangle J.2 J.1.lo) z),
    Small (f.eval z (hd.left z hz)).val B.val
  right : ∀ z (hz : representedRectangleContains (verticalIntervalRectangle J.2 J.1.hi) z),
    Small (f.eval z (hd.right z hz)).val B.val

theorem rectangleBoundaryValueBound_of_rational (f : DomainFunctions.Map)
    (hc : ContinuousOn f.domain f.eval) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hb : ∀ q, rationalRectangleBoundaryContains J q → ∀ hz, Small (f.eval (rationalRectangleScalar q) hz).val B.val) :
    RectangleBoundaryValueBound f J hd B := by
  have bound (I : QInterval × QInterval) (hx : I.1.lo≤I.1.hi) (hy : I.2.lo≤I.2.hi)
      (hdome : ∀ z : Scalar, representedRectangleContains I z → f.domain z)
      (hin : ∀ q, rationalRectangleContains I q → rationalRectangleBoundaryContains J q) :
      ∀ z (hz : representedRectangleContains I z), Small (f.eval z (hdome z hz)).val B.val := by
    apply continuousRectangle_rational_bound_extends f hc I hx hy hdome B.val
    intro q hq
    have hz := hdome _ (rationalRectangle_represented_mem I q hq)
    exact Small.congr (f.eval _ hz).property (continuousRectangleSample f I hdome q).property
      (equiv_symm (continuousRectangleSample_agreement f I hdome q hq hz)) (hb q (hin q hq) hz)
  exact ⟨bound (horizontalIntervalRectangle J.1 J.2.lo) hX Rat.le_refl hd.bottom (fun _ h => Or.inl h),
    bound (horizontalIntervalRectangle J.1 J.2.hi) hX Rat.le_refl hd.top (fun _ h => Or.inr (Or.inl h)),
    bound (verticalIntervalRectangle J.2 J.1.lo) Rat.le_refl hY hd.left (fun _ h => Or.inr (Or.inr (Or.inl h))),
    bound (verticalIntervalRectangle J.2 J.1.hi) Rat.le_refl hY hd.right (fun _ h => Or.inr (Or.inr (Or.inr h)))⟩

theorem rectangleBoundaryValueBound_of_rectangle (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hd : RectangleBoundaryDomains f J) (B : QPos)
    (hval : ∀ z (hz : representedRectangleContains J z), Small (f.eval z (hdom z hz)).val B.val) :
    RectangleBoundaryValueBound f J hd B where
  bottom := fun z hz => hval z (representedRectangle_subrectangle J (horizontalIntervalRectangle J.1 J.2.lo)
    z Rat.le_refl Rat.le_refl Rat.le_refl hY hz)
  top := fun z hz => hval z (representedRectangle_subrectangle J (horizontalIntervalRectangle J.1 J.2.hi)
    z Rat.le_refl Rat.le_refl hY Rat.le_refl hz)
  left := fun z hz => hval z (representedRectangle_subrectangle J (verticalIntervalRectangle J.2 J.1.lo)
    z Rat.le_refl hX Rat.le_refl Rat.le_refl hz)
  right := fun z hz => hval z (representedRectangle_subrectangle J (verticalIntervalRectangle J.2 J.1.hi)
    z hX Rat.le_refl Rat.le_refl Rat.le_refl hz)

end ComputableAnalysis.RiemannHilbert.RectangularContour
