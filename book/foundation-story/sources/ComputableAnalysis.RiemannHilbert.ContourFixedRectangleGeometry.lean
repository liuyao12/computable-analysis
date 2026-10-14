import ComputableAnalysis.RiemannHilbert.ContourRationalCenteredBoundary

/-! A represented interior pole supplies rational clearance from the four
edges. Small rational holes and the actual outer kernel domains are derived. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def RectanglePoleInterior (J : QInterval × QInterval) (b : Scalar) : Prop :=
  ∃ D : QPos, representedRectangleContains
    (⟨J.1.lo+D.val,J.1.hi-D.val⟩,⟨J.2.lo+D.val,J.2.hi-D.val⟩) b

theorem rectanglePoleInterior_ordered (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) : J.1.lo≤J.1.hi ∧ J.2.lo≤J.2.hi := by
  obtain ⟨D,hb⟩ := hb
  have hx := RealRaw.le_trans (realPart_valid b.property) hb.1 hb.2.1
  have hy := RealRaw.le_trans (imagPart_valid b.property) hb.2.2.1 hb.2.2.2
  have hxx := hx 0 0
  have hyy := hy 0 0
  change J.1.lo+D.val≤J.1.hi-D.val at hxx
  change J.2.lo+D.val≤J.2.hi-D.val at hyy
  have hp := D.property
  constructor <;> grind only

theorem rectanglePoleInterior_mem (J : QInterval × QInterval) (b : Scalar)
    (hb : RectanglePoleInterior J b) : representedRectangleContains J b := by
  obtain ⟨D,hb⟩ := hb
  have hp := D.property
  exact representedRectangle_subrectangle J
    (⟨J.1.lo+D.val,J.1.hi-D.val⟩,⟨J.2.lo+D.val,J.2.hi-D.val⟩) b
    (by grind only) (by grind only) (by grind only) (by grind only) hb

def selfRectangleRibbon (J : QInterval × QInterval) (b : Scalar) (hb : RectanglePoleInterior J b) :
    RectangleRibbon where
  outer := J
  inner := J
  xLo := Rat.le_refl
  xOrder := (rectanglePoleInterior_ordered J b hb).1
  xHi := Rat.le_refl
  yLo := Rat.le_refl
  yOrder := (rectanglePoleInterior_ordered J b hb).2
  yHi := Rat.le_refl

theorem rectangleCauchyBoundaryDomains (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) : RectangleBoundaryDomains (ribbonCauchyKernel f b) J :=
  ribbonOuterDomains _ (selfRectangleRibbon J b hb)
    (ribbonCauchyKernel_domain f _ (ribbonDomain_of_outer f _ hdom) b hb)

def fixedRectangleCauchyContour (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (n : Nat) : Scalar :=
  continuousRectangleBoundary (ribbonCauchyKernel f b) J (rectangleCauchyBoundaryDomains f J hdom b hb) n

theorem rationalPoleHole_nested (J : QInterval × QInterval) (b : Scalar) (D R : QPos)
    (hb : representedRectangleContains (⟨J.1.lo+D.val,J.1.hi-D.val⟩,⟨J.2.lo+D.val,J.2.hi-D.val⟩) b)
    (n : Nat) (hR : 3*R.val≤D.val) :
    J.1.lo≤(rationalCenteredRectangle (rationalPoleCenter b R n) R.val).1.lo ∧
    (rationalCenteredRectangle (rationalPoleCenter b R n) R.val).1.hi≤J.1.hi ∧
    J.2.lo≤(rationalCenteredRectangle (rationalPoleCenter b R n) R.val).2.lo ∧
    (rationalCenteredRectangle (rationalPoleCenter b R n) R.val).2.hi≤J.2.hi := by
  let c := rationalPoleCenter b R n
  have hc := rationalPoleCenter_half_square b R n
  have hx0 := (RealRaw.le_trans (realPart_valid b.property) hb.1 hc.2.1) 0 0
  have hx1 := (RealRaw.le_trans (realPart_valid b.property) hc.1 hb.2.1) 0 0
  have hy0 := (RealRaw.le_trans (imagPart_valid b.property) hb.2.2.1 hc.2.2.2) 0 0
  have hy1 := (RealRaw.le_trans (imagPart_valid b.property) hc.2.2.1 hb.2.2.2) 0 0
  change J.1.lo+D.val≤c.re+R.val/2 at hx0
  change c.re-R.val/2≤J.1.hi-D.val at hx1
  change J.2.lo+D.val≤c.im+R.val/2 at hy0
  change c.im-R.val/2≤J.2.hi-D.val at hy1
  change J.1.lo≤c.re-R.val ∧ c.re+R.val≤J.1.hi ∧ J.2.lo≤c.im-R.val ∧ c.im+R.val≤J.2.hi
  have hp := R.property
  grind only

def rationalPoleHoleRibbon (J : QInterval × QInterval) (b : Scalar) (D R : QPos)
    (hb : representedRectangleContains (⟨J.1.lo+D.val,J.1.hi-D.val⟩,⟨J.2.lo+D.val,J.2.hi-D.val⟩) b)
    (n : Nat) (hR : 3*R.val≤D.val) : RectangleRibbon where
  outer := J
  inner := rationalCenteredRectangle (rationalPoleCenter b R n) R.val
  xLo := (rationalPoleHole_nested J b D R hb n hR).1
  xOrder := (rationalCenteredRectangle_ordered _ R).1
  xHi := (rationalPoleHole_nested J b D R hb n hR).2.1
  yLo := (rationalPoleHole_nested J b D R hb n hR).2.2.1
  yOrder := (rationalCenteredRectangle_ordered _ R).2
  yHi := (rationalPoleHole_nested J b D R hb n hR).2.2.2

theorem rationalPoleHole_inside (J : QInterval × QInterval) (b : Scalar) (D R : QPos)
    (hb : representedRectangleContains (⟨J.1.lo+D.val,J.1.hi-D.val⟩,⟨J.2.lo+D.val,J.2.hi-D.val⟩) b)
    (n : Nat) (hR : 3*R.val≤D.val) : RibbonPoleInterior (rationalPoleHoleRibbon J b D R hb n hR) b := by
  let H : QPos := ⟨R.val/2,by rw [Rat.div_def]; exact Rat.mul_pos R.property (by decide +kernel)⟩
  refine ⟨H,?_⟩
  have hx (x : Rat) : x-R.val+H.val=x-R.val/2 := by dsimp [H]; grind only
  have hy (x : Rat) : x+R.val-H.val=x+R.val/2 := by dsimp [H]; grind only
  simpa only [rationalPoleHoleRibbon,rationalCenteredRectangle,hx,hy] using rationalPoleCenter_half_square b R n

end ComputableAnalysis.RiemannHilbert.RectangularContour
