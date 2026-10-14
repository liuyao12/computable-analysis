import ComputableAnalysis.RiemannHilbert.ContourConstructedMoments

/-! Actual power-kernel boundaries deform through a certified pole-free
rectangle ribbon. A common rational intersection compares arbitrary rectangles
enclosing the same represented pole. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def commonRectangle (J K : QInterval × QInterval) : QInterval × QInterval :=
  (⟨max J.1.lo K.1.lo,min J.1.hi K.1.hi⟩,⟨max J.2.lo K.2.lo,min J.2.hi K.2.hi⟩)

theorem commonRectangle_pole_inside (J K : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior K b) : RectanglePoleInterior (commonRectangle J K) b := by
  obtain ⟨D,hD⟩ := hb
  obtain ⟨E,hE⟩ := hc
  let H := minRadius D E
  have hd := minRadius_left D E
  have he := minRadius_right D E
  refine ⟨H,?_,?_,?_,?_⟩ <;> intro n m
  · have hj := hD.1 n m; have hk := hE.1 n m
    change J.1.lo+D.val≤(b.val.compute m).hi.re at hj
    change K.1.lo+E.val≤(b.val.compute m).hi.re at hk
    change max J.1.lo K.1.lo+H.val≤(b.val.compute m).hi.re
    grind
  · have hj := hD.2.1 n m; have hk := hE.2.1 n m
    change (b.val.compute n).lo.re≤J.1.hi-D.val at hj
    change (b.val.compute n).lo.re≤K.1.hi-E.val at hk
    change (b.val.compute n).lo.re≤min J.1.hi K.1.hi-H.val
    grind
  · have hj := hD.2.2.1 n m; have hk := hE.2.2.1 n m
    change J.2.lo+D.val≤(b.val.compute m).hi.im at hj
    change K.2.lo+E.val≤(b.val.compute m).hi.im at hk
    change max J.2.lo K.2.lo+H.val≤(b.val.compute m).hi.im
    grind
  · have hj := hD.2.2.2 n m; have hk := hE.2.2.2 n m
    change (b.val.compute n).lo.im≤J.2.hi-D.val at hj
    change (b.val.compute n).lo.im≤K.2.hi-E.val at hk
    change (b.val.compute n).lo.im≤min J.2.hi K.2.hi-H.val
    grind

def commonRectangleRibbon (J K : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior K b) : RectangleRibbon where
  outer := J
  inner := commonRectangle J K
  xLo := by dsimp [commonRectangle]; grind
  xOrder := (rectanglePoleInterior_ordered _ b (commonRectangle_pole_inside J K b hb hc)).1
  xHi := by dsimp [commonRectangle]; grind
  yLo := by dsimp [commonRectangle]; grind
  yOrder := (rectanglePoleInterior_ordered _ b (commonRectangle_pole_inside J K b hb hc)).2
  yHi := by dsimp [commonRectangle]; grind

theorem commonRectangle_domain (f : DomainFunctions.Map) (J K : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) :
    ∀ z, representedRectangleContains (commonRectangle J K) z → f.domain z := by
  intro z hz
  apply hdom z
  apply representedRectangle_subrectangle J (commonRectangle J K) z _ _ _ _ hz <;>
    dsimp [commonRectangle] <;> grind

theorem fixedRectanglePowerContour_nested_difference (f : DomainFunctions.Map) (hf : Holomorphic f)
    (G : RectangleRibbon) (hJ : ∀ z, representedRectangleContains G.outer z → f.domain z)
    (hK : ∀ z, representedRectangleContains G.inner z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior G.outer b) (hc : RectanglePoleInterior G.inner b) (m : Nat) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (sub (fixedRectanglePowerContour f G.outer hJ b hb m n).val
      (fixedRectanglePowerContour f G.inner hK b hc m n).val) eps.val :=
  ribbonDifference_eventual_zero (ribbonCauchyPowerKernel f b m) (ribbonCauchyPowerKernel_holomorphic f hf b m) G
    (ribbonCauchyKernel_domain f G (ribbonDomain_of_outer f G hJ) b hc) eps

theorem fixedRectanglePowerContour_nested_limits_agree (f : DomainFunctions.Map) (hf : Holomorphic f)
    (G : RectangleRibbon) (hJ : ∀ z, representedRectangleContains G.outer z → f.domain z)
    (hK : ∀ z, representedRectangleContains G.inner z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior G.outer b) (hc : RectanglePoleInterior G.inner b) (m : Nat)
    (u v : Scalar) (hu : Converges (fixedRectanglePowerContour f G.outer hJ b hb m) u)
    (hv : Converges (fixedRectanglePowerContour f G.inner hK b hc m) v) : u≈v :=
  ribbonBoundary_limits_agree (ribbonCauchyPowerKernel f b m) (ribbonCauchyPowerKernel_holomorphic f hf b m) G
    (ribbonCauchyKernel_domain f G (ribbonDomain_of_outer f G hJ) b hc) u v hu hv

theorem fixedRectanglePowerContour_rectangles_agree (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J K : QInterval × QInterval)
    (hJ : ∀ z, representedRectangleContains J z → f.domain z)
    (hK : ∀ z, representedRectangleContains K z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior K b) (m : Nat)
    (u v : Scalar) (hu : Converges (fixedRectanglePowerContour f J hJ b hb m) u)
    (hv : Converges (fixedRectanglePowerContour f K hK b hc m) v) : u≈v := by
  let H := commonRectangle J K
  let hH := commonRectangle_domain f J K hJ
  let hp := commonRectangle_pole_inside J K b hb hc
  let G := commonRectangleRibbon J K b hb hc
  let G' : RectangleRibbon := {
    outer := K
    inner := H
    xLo := by dsimp [H,commonRectangle]; grind
    xOrder := (rectanglePoleInterior_ordered H b hp).1
    xHi := by dsimp [H,commonRectangle]; grind
    yLo := by dsimp [H,commonRectangle]; grind
    yOrder := (rectanglePoleInterior_ordered H b hp).2
    yHi := by dsimp [H,commonRectangle]; grind }
  have hcommon : Converges (fixedRectanglePowerContour f H hH b hp m) u := by
    apply converge_perturbation _ _ u hu
    intro eps
    obtain ⟨N,hN⟩ := fixedRectanglePowerContour_nested_difference f hf G hJ hH b hb hp m eps
    exact ⟨N,fun n hn => RepresentedCauchySum.small_sub_symm _ _ _ (hN n hn)⟩
  exact equiv_symm (fixedRectanglePowerContour_nested_limits_agree f hf G' hK hH b hc hp m v u hv hcommon)

end ComputableAnalysis.RiemannHilbert.RectangularContour
