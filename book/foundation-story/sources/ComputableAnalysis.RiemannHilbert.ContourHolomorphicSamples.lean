import ComputableAnalysis.RiemannHilbert.ContourCellEstimates
import ComputableAnalysis.RiemannHilbert.ContourNeighborhoodCover

/-! Actual holomorphic samples and proved local affine sample errors. Adapted from the corresponding finite rectangle proofs in
`ComputableAnalysis.ModularForms`, with only the generic dependencies retained. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option autoImplicit false

def holomorphicRectangleSample (f : DomainFunctions.Map) (_hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z) (q : QComplex) : Scalar :=
  if h : rationalRectangleContains J q then
    (f).eval (rationalRectangleScalar q)
      (hdom _ (rationalRectangle_represented_mem J q h))
  else ⟨zero,ofQComplex_valid _⟩

theorem holomorphicRectangleSample_agreement (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (q : QComplex) (hq : rationalRectangleContains J q)
    (hz : (f).domain (rationalRectangleScalar q)) :
    ((f).eval (rationalRectangleScalar q) hz).val.Equiv
      (holomorphicRectangleSample f hf J hdom q).val := by
  simp only [holomorphicRectangleSample,dif_pos hq]
  exact equiv_refl _ ((f).eval (rationalRectangleScalar q) hz).property

theorem holomorphicRectangleSample_model_error (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (c : Scalar) (hc : (f).domain c)
    (p q : QComplex) (hp : rationalRectangleContains J p) (hq : rationalRectangleContains J q)
    (W eps : QPos) (hd : Small (sub (ofQComplex q) (ofQComplex p)) W.val)
    (hpc : Small (Centered.offset c (rationalRectangleScalar p)).val
      ((hf).continuousDerivative.delta c hc eps).val)
    (hqc : Small (Centered.offset c (rationalRectangleScalar q)).val
      ((hf).continuousDerivative.delta c hc eps).val) :
    Small (sub (holomorphicRectangleSample f hf J hdom q).val
      (affineMidpointModel (holomorphicRectangleSample f hf J hdom p)
        ((hf).derivative c hc)
        (Centered.offset (rationalRectangleScalar p) (rationalRectangleScalar q))).val)
      (4*eps.val*W.val) := by
  let d := hf.derivative c hc
  let P := rationalRectangleScalar p
  let Q := rationalRectangleScalar q
  have hP : f.domain P := hdom P
    (rationalRectangle_represented_mem J p hp)
  have hQ : f.domain Q := hdom Q
    (rationalRectangle_represented_mem J q hq)
  have hr := domainNeighborhood_segment_remainder_bound f hf c P Q hc hP hQ W eps
    (fun t => hdom _
      (representedAffine_rational_rectangle_mem J p q hp hq t)) hd hpc hqc
  have hb := Small.congr (DomainFunctions.remainder_valid f P hP d Q hQ)
    (sub_valid (f.eval Q hQ).property (affineMidpointModel (f.eval P hP) d (Centered.offset P Q)).property)
    (equiv_symm (localAffineModel_error_equiv f P d Q hP hQ)) hr
  simp only [holomorphicRectangleSample,dif_pos hp,dif_pos hq]
  exact hb


theorem holomorphicRectangleSample_cycle_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (c : Scalar) (hc : (f).domain c) (eps H : QPos)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hx : J.1.width≤2*H.val) (hy : J.2.width≤2*H.val)
    (hnear : ∀ q : QComplex, rationalRectangleContains J q →
      Small (Centered.offset c (rationalRectangleScalar q)).val
        ((hf).continuousDerivative.delta c hc eps).val) :
    Small (fullRectangleMidpointCycle (holomorphicRectangleSample f hf J hdom) J).val
      (64*eps.val*H.val*H.val) := by
  have hm := (rectangleMidpoints_mem J hX hY).1
  have hb := rectangleSampleModel_full_cycle_bound (holomorphicRectangleSample f hf J hdom) J
    ((hf).derivative c hc) (4*eps.val*H.val) H
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property))
      (Rat.le_of_lt H.property)) hX hY hx hy
    (fun q hq hd => holomorphicRectangleSample_model_error f hf J hdom c hc
      (rectangleCenter J) q hm hq H eps hd (hnear _ hm) (hnear _ hq))
  have he : 16*(4*eps.val*H.val)*H.val=64*eps.val*H.val*H.val := by grind only
  rw [he] at hb
  exact hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
