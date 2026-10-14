import ComputableAnalysis.RiemannHilbert.ContourDerivativeLipschitz

/-! Explicit derivative bounds on actual represented edges give quantitative
sample comparisons. A bound is required along the whole edge, including every
represented affine segment, rather than only at the quadrature tags. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem continuousRectangleSample_derivative_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z) (B : QPos)
    (hder : ∀ z (hz : representedRectangleContains J z), Small (hf.derivative z (hdom z hz)).val B.val)
    (p q : QComplex) (hp : rationalRectangleContains J p) (hq : rationalRectangleContains J q)
    (H : QPos) (hd : Small (sub (ofQComplex q) (ofQComplex p)) H.val) :
    Small (sub (continuousRectangleSample f J hdom q).val
      (continuousRectangleSample f J hdom p).val) (4*B.val*H.val) := by
  have hp' := rationalRectangle_represented_mem J p hp
  have hq' := rationalRectangle_represented_mem J q hq
  have hs := domainSegment_difference_bound f hf (rationalRectangleScalar p) (rationalRectangleScalar q)
    (hdom _ hp') (hdom _ hq') H B
    (fun t => hdom _ (representedAffine_rational_rectangle_mem J p q hp hq t)) hd
    (fun t => hder _ (representedAffine_rational_rectangle_mem J p q hp hq t))
  exact Small.congr (sub_valid (f.eval _ (hdom _ hq')).property (f.eval _ (hdom _ hp')).property)
    (sub_valid (continuousRectangleSample f J hdom q).property (continuousRectangleSample f J hdom p).property)
    (FunctionTheory.sub_congr
      (equiv_symm (continuousRectangleSample_agreement f J hdom q hq (hdom _ hq')))
      (equiv_symm (continuousRectangleSample_agreement f J hdom p hp (hdom _ hp')))) hs

theorem horizontalIntervalSample_derivative_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (I : QInterval) (y : Rat)
    (hdom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (B : QPos)
    (hder : ∀ z (hz : representedRectangleContains (horizontalIntervalRectangle I y) z),
      Small (hf.derivative z (hdom z hz)).val B.val)
    (p q : Rat) (hp : I.lo≤p ∧ p≤I.hi) (hq : I.lo≤q ∧ q≤I.hi)
    (H : QPos) (hl : -H.val≤q-p) (hu : q-p≤H.val) :
    Small (sub (horizontalIntervalSample f I y hdom q).val
      (horizontalIntervalSample f I y hdom p).val) (4*B.val*H.val) := by
  apply continuousRectangleSample_derivative_bound f hf (horizontalIntervalRectangle I y) hdom B hder
    (⟨p,y⟩ : QComplex) (⟨q,y⟩ : QComplex)
    ⟨hp.1,hp.2,Rat.le_refl,Rat.le_refl⟩ ⟨hq.1,hq.2,Rat.le_refl,Rat.le_refl⟩ H
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · change -H.val≤q + -p; grind only
  · change q + -p≤H.val; grind only
  · change -H.val≤y + -y; have h := H.property; grind only
  · change y + -y≤H.val; have h := H.property; grind only

theorem verticalIntervalSample_derivative_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (I : QInterval) (x : Rat)
    (hdom : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (B : QPos)
    (hder : ∀ z (hz : representedRectangleContains (verticalIntervalRectangle I x) z),
      Small (hf.derivative z (hdom z hz)).val B.val)
    (p q : Rat) (hp : I.lo≤p ∧ p≤I.hi) (hq : I.lo≤q ∧ q≤I.hi)
    (H : QPos) (hl : -H.val≤q-p) (hu : q-p≤H.val) :
    Small (sub (verticalIntervalSample f I x hdom q).val
      (verticalIntervalSample f I x hdom p).val) (4*B.val*H.val) := by
  apply continuousRectangleSample_derivative_bound f hf (verticalIntervalRectangle I x) hdom B hder
    (⟨x,p⟩ : QComplex) (⟨x,q⟩ : QComplex)
    ⟨Rat.le_refl,Rat.le_refl,hp.1,hp.2⟩ ⟨Rat.le_refl,Rat.le_refl,hq.1,hq.2⟩ H
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · change -H.val≤x + -x; have h := H.property; grind only
  · change x + -x≤H.val; have h := H.property; grind only
  · change -H.val≤q + -p; grind only
  · change q + -p≤H.val; grind only

end ComputableAnalysis.RiemannHilbert.RectangularContour
