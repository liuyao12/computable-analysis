import ComputableAnalysis.RiemannHilbert.ContourRibbonPole

/-! Actual ribbon sums and shifted kernels respect equivalent represented
values. In particular, a different valid pole name preserves the computation. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem continuousRectangleBoundary_eval_congr (f g : DomainFunctions.Map) (J : QInterval × QInterval)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hf : RectangleBoundaryDomains f J) (hg : RectangleBoundaryDomains g J)
    (he : ∀ z (hfz : f.domain z) (hgz : g.domain z), f.eval z hfz ≈ g.eval z hgz) (n : Nat) :
    continuousRectangleBoundary f J hf n ≈ continuousRectangleBoundary g J hg n :=
  add_equiv (FunctionTheory.sub_congr
    (horizontalContinuousPrefix_congr f g J.1 J.2.lo hX hf.bottom hg.bottom
      (fun z hz => he z (hf.bottom z hz) (hg.bottom z hz)) n)
    (horizontalContinuousPrefix_congr f g J.1 J.2.hi hX hf.top hg.top
      (fun z hz => he z (hf.top z hz) (hg.top z hz)) n))
    (FunctionTheory.sub_congr
      (verticalContinuousPrefix_congr f g J.2 J.1.hi hY hf.right hg.right
        (fun z hz => he z (hf.right z hz) (hg.right z hz)) n)
      (verticalContinuousPrefix_congr f g J.2 J.1.lo hY hf.left hg.left
        (fun z hz => he z (hf.left z hz) (hg.left z hz)) n))

theorem ribbonDifference_eval_congr (f g : DomainFunctions.Map) (G : RectangleRibbon)
    (hf : RibbonDomain f G) (hg : RibbonDomain g G)
    (he : ∀ z (hfz : f.domain z) (hgz : g.domain z), f.eval z hfz ≈ g.eval z hgz) (n : Nat) :
    ribbonDifference f G hf n ≈ ribbonDifference g G hg n :=
  FunctionTheory.sub_congr
    (continuousRectangleBoundary_eval_congr f g G.outer (ribbon_outer_x_order G) (ribbon_outer_y_order G)
      (ribbonOuterDomains f G hf) (ribbonOuterDomains g G hg) he n)
    (continuousRectangleBoundary_eval_congr f g G.inner G.xOrder G.yOrder
      (ribbonInnerDomains f G hf) (ribbonInnerDomains g G hg) he n)

theorem ribbonPoleInterior_congr (G : RectangleRibbon) (b c : Scalar) (he : b≈c) (hb : RibbonPoleInterior G b) :
    RibbonPoleInterior G c := by
  obtain ⟨R,hR⟩ := hb
  exact ⟨R,representedRectangle_congr _ b c he hR⟩

theorem ribbonPoleReciprocal_congr (b c z : Scalar) (he : b≈c)
    (hb : (ribbonPoleReciprocal b).domain z) (hc : (ribbonPoleReciprocal c).domain z) :
    (ribbonPoleReciprocal b).eval z hb ≈ (ribbonPoleReciprocal c).eval z hc :=
  RepresentedReciprocal.inverse_congr _ _ (compose_outer_mem hb) (compose_outer_mem hc)
    (add_equiv (neg_equiv he) (equiv_refl _ (mul_valid oneScalar.property z.property)))

theorem ribbonCauchyKernel_pole_congr (f : DomainFunctions.Map) (b c z : Scalar) (he : b≈c)
    (hb : (ribbonCauchyKernel f b).domain z) (hc : (ribbonCauchyKernel f c).domain z) :
    (ribbonCauchyKernel f b).eval z hb ≈ (ribbonCauchyKernel f c).eval z hc :=
  mul_equiv (f.eval z hb.1).property (f.eval z hc.1).property
    ((ribbonPoleReciprocal b).eval z hb.2).property ((ribbonPoleReciprocal c).eval z hc.2).property
    (equiv_refl _ (f.eval z hb.1).property) (ribbonPoleReciprocal_congr b c z he hb.2 hc.2)

theorem ribbonCauchyKernelDifference_pole_congr (f : DomainFunctions.Map) (G : RectangleRibbon)
    (hd : RibbonDomain f G) (b c : Scalar) (he : b≈c)
    (hb : RibbonPoleInterior G b) (hc : RibbonPoleInterior G c) (n : Nat) :
    ribbonDifference (ribbonCauchyKernel f b) G (ribbonCauchyKernel_domain f G hd b hb) n ≈
      ribbonDifference (ribbonCauchyKernel f c) G (ribbonCauchyKernel_domain f G hd c hc) n :=
  ribbonDifference_eval_congr _ _ G (ribbonCauchyKernel_domain f G hd b hb)
    (ribbonCauchyKernel_domain f G hd c hc) (fun z hzb hzc => ribbonCauchyKernel_pole_congr f b c z he hzb hzc) n

end ComputableAnalysis.RiemannHilbert.RectangularContour
