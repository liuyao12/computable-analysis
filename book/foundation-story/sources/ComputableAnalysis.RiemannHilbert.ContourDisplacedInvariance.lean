import ComputableAnalysis.RiemannHilbert.ContourDisplacedNormalized
import ComputableAnalysis.RiemannHilbert.ContourRibbonInvariance
import ComputableAnalysis.RiemannHilbert.ContourSamplerAgreement

/-! Actual pole names agree on a common rational frame. Independently chosen
rational centers and local radii are reconciled by their proved limits. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def displacedFrameFunction_holomorphic (f : DomainFunctions.Map) (hf : Holomorphic f) (b c : Scalar) :
    Holomorphic (displacedFrameFunction f b c) :=
  (ribbonCauchyKernel_holomorphic f hf b).compose (DomainFunctions.affine_holomorphic c oneScalar)

theorem displacedFrameFunction_pole_congr (f : DomainFunctions.Map) (b d c z : Scalar) (he : b≈d)
    (hb : (displacedFrameFunction f b c).domain z) (hd : (displacedFrameFunction f d c).domain z) :
    (displacedFrameFunction f b c).eval z hb ≈ (displacedFrameFunction f d c).eval z hd :=
  ribbonCauchyKernel_pole_congr f b d ((kernelTranslation c).eval z trivial) he
    (compose_outer_mem hb) (compose_outer_mem hd)

theorem displacedFrameSample_pole_congr (f : DomainFunctions.Map) (b d c : Scalar) (he : b≈d) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate c z))
    (hb : Small (Centered.offset c b).val (R.val/64))
    (hd : Small (Centered.offset c d).val (R.val/64)) (q : QComplex) :
    displacedFrameSample f b c R hdom hb q ≈ displacedFrameSample f d c R hdom hd q :=
  frameSample_congr _ _ R (displacedFrame_domain f b c R hdom hb)
    (displacedFrame_domain f d c R hdom hd)
    (fun z _ => displacedFrameFunction_pole_congr f b d c z he _ _) q

theorem displacedInnerPrefix_pole_congr (f : DomainFunctions.Map) (b d c : Scalar) (he : b≈d) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain (Centered.translate c z))
    (hb : Small (Centered.offset c b).val (R.val/64))
    (hd : Small (Centered.offset c d).val (R.val/64)) (M : Nat) (hM : 0<M) :
    displacedInnerPrefix f b c R hdom hb M ≈ displacedInnerPrefix f d c R hdom hd M :=
  innerBoundary_congr_on_frame _ _ R M hM (fun q _ => displacedFrameSample_pole_congr f b d c he R hdom hb hd q)

end ComputableAnalysis.RiemannHilbert.RectangularContour
