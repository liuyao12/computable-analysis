import ComputableAnalysis.RiemannHilbert.ContourPolePerturbation
import ComputableAnalysis.RiemannHilbert.ContourRibbonPole

/-! A small represented displacement preserves separation of every point
of the rational square frame, not only its finitely sampled tags. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions BoxApproximation
set_option autoImplicit false

theorem frameDomain_not_small (R : QPos) (z : Scalar) (hz : frameDomain R z)
    (H : Rat) (hHR : H<R.val) : ¬Small z.val H := by
  obtain ⟨j,k,hi,hz⟩ := hz
  intro hs
  rcases squareFrameTile_separated R j k hi with hx|hx|hy|hy
  · have h := RealRaw.le_trans (realPart_valid z.property) hz.1 hs.2.1
    have hh := h 0 0
    change (squareFrameTile R j k).1.lo≤H at hh
    grind only
  · have h := RealRaw.le_trans (realPart_valid z.property) hs.1 hz.2.1
    have hh := h 0 0
    change -H≤(squareFrameTile R j k).1.hi at hh
    grind only
  · have h := RealRaw.le_trans (imagPart_valid z.property) hz.2.2.1 hs.2.2.2
    have hh := h 0 0
    change (squareFrameTile R j k).2.lo≤H at hh
    grind only
  · have h := RealRaw.le_trans (imagPart_valid z.property) hs.2.2.1 hz.2.2.2
    have hh := h 0 0
    change -H≤(squareFrameTile R j k).2.hi at hh
    grind only

theorem offset_zero_agreement (d z : Scalar) (hz : (Centered.offset d z).val.Equiv zero) : z≈d := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (Centered.offset d z).property) (hright := ofQComplex_valid _) hz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property) (hright := d.property)
  change gridScalarValue z-gridScalarValue d=0 at he
  change gridScalarValue z=gridScalarValue d
  grind only

theorem displacedFrame_nonzero (R : QPos) (d : Scalar) (hd : Small d.val (R.val/64))
    (z : Scalar) (hz : frameDomain R z) : NonzeroBoxSearch.Nonzero (Centered.offset d z) := by
  intro he
  have hs := Small.congr d.property z.property (equiv_symm (offset_zero_agreement d z he)) hd
  exact frameDomain_not_small R z hz (R.val/64) (by have hp := R.property; grind only) hs

theorem displacedOffset_agreement (b c z : Scalar) :
    Centered.offset b (Centered.translate c z) ≈ Centered.offset (Centered.offset c b) z := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Centered.offset b (Centered.translate c z)).property)
    (hright := (Centered.offset (Centered.offset c b) z).property)
  change (gridScalarValue c+gridScalarValue z)-gridScalarValue b=
    gridScalarValue z-(gridScalarValue b-gridScalarValue c)
  grind only

theorem displacedTranslate_distance (b c z : Scalar) (R H : Rat)
    (hz : Small z.val R) (hc : Small (Centered.offset c b).val H) :
    Small (Centered.offset b (Centered.translate c z)).val (R+H) := by
  have hs := SeriesLimitLaws.small_sub hz hc
  exact Small.congr (Centered.offset (Centered.offset c b) z).property
    (Centered.offset b (Centered.translate c z)).property
    (equiv_symm (displacedOffset_agreement b c z)) hs

def displacedFrameFunction (f : DomainFunctions.Map) (b c : Scalar) : DomainFunctions.Map :=
  DomainFunctions.compose (ribbonCauchyKernel f b) (kernelTranslation c)

def displacedFrame_domain (f : DomainFunctions.Map) (b c : Scalar) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate c z))
    (hc : Small (Centered.offset c b).val (R.val/64)) :
    ∀ z, frameDomain R z → (displacedFrameFunction f b c).domain z := by
  intro z hz
  let v := (kernelTranslation c).eval z trivial
  have he : v≈Centered.translate c z := kernelTranslation_agreement c z
  have hn : NonzeroBoxSearch.Nonzero (Centered.offset b v) := by
    apply (NonzeroBoxSearch.nonzero_congr (Centered.offset (Centered.offset c b) z) (Centered.offset b v) _).1
      (displacedFrame_nonzero R _ hc z hz)
    exact Setoid.trans (Setoid.symm (displacedOffset_agreement b c z))
      (FunctionTheory.sub_congr (equiv_symm he) (equiv_refl _ b.property))
  refine ⟨trivial,?_,trivial,?_⟩
  · exact (f.domain_congr v (Centered.translate c z) he).mpr (hdom z hz)
  · exact (NonzeroBoxSearch.nonzero_congr (Centered.offset b v) ((ribbonPoleOffset b).eval v trivial)
      (equiv_symm (ribbonPoleOffset_agreement b v))).mp hn

def displacedFrameSample (f : DomainFunctions.Map) (b c : Scalar) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate c z))
    (hc : Small (Centered.offset c b).val (R.val/64)) : QComplex → Scalar :=
  frameSample (displacedFrameFunction f b c) R (displacedFrame_domain f b c R hdom hc)

theorem displacedFrameSample_value (f : DomainFunctions.Map) (b c : Scalar) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate c z))
    (hc : Small (Centered.offset c b).val (R.val/64)) (q : QComplex)
    (hq : frameDomain R (rationalRectangleScalar q)) :
    displacedFrameSample f b c R hdom hc q ≈
      scalarProduct (f.eval (Centered.translate c (rationalRectangleScalar q)) (hdom _ hq))
        (RepresentedReciprocal.inverse (Centered.offset (Centered.offset c b) (rationalRectangleScalar q))
          (displacedFrame_nonzero R _ hc _ hq)) := by
  let z := rationalRectangleScalar q
  let v := (kernelTranslation c).eval z trivial
  let hv := displacedFrame_domain f b c R hdom hc z hq
  have he : v≈Centered.translate c z := kernelTranslation_agreement c z
  have hn : NonzeroBoxSearch.Nonzero (Centered.offset b v) := by
    apply (NonzeroBoxSearch.nonzero_congr _ _ (ribbonPoleOffset_agreement b v)).mp
      (compose_outer_mem hv).2.2
  have hval := ribbonCauchyKernel_value f b v (compose_outer_mem hv) hn
  refine Setoid.trans (frameSample_on_frame _ R _ q hq) ?_
  refine Setoid.trans hval ?_
  exact mul_equiv (f.eval v (compose_outer_mem hv).1).property
    (f.eval _ (hdom _ hq)).property (RepresentedReciprocal.inverse _ hn).property
    (RepresentedReciprocal.inverse _ _).property
    (f.eval_congr _ _ _ _ he)
    (RepresentedReciprocal.inverse_congr _ _ hn _
      (Setoid.trans (FunctionTheory.sub_congr he (equiv_refl _ b.property)) (displacedOffset_agreement b c z)))

end ComputableAnalysis.RiemannHilbert.RectangularContour
