import ComputableAnalysis.RiemannHilbert.ContourDisplacedBounds
import ComputableAnalysis.RiemannHilbert.ContourLocalCauchyRate

/-! Executable rational centers are chosen more accurately than the shrinking
radius. Whole translated frames remain in the supplied actual open domain. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions BoxApproximation
set_option autoImplicit false

def poleCenterTolerance (R : QPos) (n : Nat) : QPos :=
  ⟨R.val*((1:Rat)/2)^n/64,by
    rw [Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos R.property (Rat.pow_pos (by decide +kernel)))
      (by decide +kernel)⟩

def rationalPoleCenter (b : Scalar) (R : QPos) (n : Nat) : QComplex :=
  (b.val.compute (PrecisionSearch.stage b.val b.property (poleCenterTolerance R n))).center

def representedPoleCenter (b : Scalar) (R : QPos) (n : Nat) : Scalar :=
  rationalRectangleScalar (rationalPoleCenter b R n)

theorem poleCenterTolerance_relative (R : QPos) (n : Nat) : (poleCenterTolerance R n).val≤R.val/64 := by
  have h := Rat.mul_le_mul_of_nonneg_left (half_power_le_one n) (Rat.le_of_lt R.property)
  have hm := Rat.mul_le_mul_of_nonneg_right h (show (0:Rat)≤(64:Rat)⁻¹ by decide +kernel)
  simpa only [poleCenterTolerance,Rat.div_def,Rat.mul_one] using hm

theorem rationalPoleCenter_error (b : Scalar) (R : QPos) (n : Nat) :
    Small (Centered.offset (representedPoleCenter b R n) b).val (poleCenterTolerance R n).val := by
  have h := PrecisionSearch.stage_spec b.val b.property (poleCenterTolerance R n)
  exact center_error b _ _ (Rat.le_of_lt (poleCenterTolerance R n).property) h.1 h.2

def rationalCenteredRectangle (c : QComplex) (R : Rat) : QInterval × QInterval :=
  (⟨c.re-R,c.re+R⟩,⟨c.im-R,c.im+R⟩)

theorem rationalCenteredRectangle_mem (c : QComplex) (b : Scalar) (R : Rat)
    (hb : Small (Centered.offset (rationalRectangleScalar c) b).val R) :
    representedRectangleContains (rationalCenteredRectangle c R) b := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro n m
  · have h := hb.1 n m
    change -R≤(b.val.compute m).hi.re + -c.re at h
    change c.re-R≤(b.val.compute m).hi.re
    grind only
  · have h := hb.2.1 n m
    change (b.val.compute n).lo.re + -c.re≤R at h
    change (b.val.compute n).lo.re≤c.re+R
    grind only
  · have h := hb.2.2.1 n m
    change -R≤(b.val.compute m).hi.im + -c.im at h
    change c.im-R≤(b.val.compute m).hi.im
    grind only
  · have h := hb.2.2.2 n m
    change (b.val.compute n).lo.im + -c.im≤R at h
    change (b.val.compute n).lo.im≤c.im+R
    grind only

theorem rationalPoleCenter_half_square (b : Scalar) (R : QPos) (n : Nat) :
    representedRectangleContains (rationalCenteredRectangle (rationalPoleCenter b R n) (R.val/2)) b := by
  have h := poleCenterTolerance_relative R n
  have hp := R.property
  exact rationalCenteredRectangle_mem _ b _ ((rationalPoleCenter_error b R n).mono (by grind only))

theorem rationalFrame_distance (b : Scalar) (R : QPos) (n : Nat) (z : Scalar) (hz : frameDomain R z) :
    Small (Centered.offset b (Centered.translate (representedPoleCenter b R n) z)).val (3*R.val) := by
  have hs := displacedTranslate_distance b (representedPoleCenter b R n) z (2*R.val) (R.val/64)
    (frameDomain_bound R z hz) ((rationalPoleCenter_error b R n).mono (poleCenterTolerance_relative R n))
  exact hs.mono (by have hp := R.property; grind only)

def displacedLocalCenter (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (n : Nat) : Scalar :=
  representedPoleCenter b (shrinkingContourRadius f hf b hb n) n

def displacedLocalFrame_domain (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (n : Nat) :
    ∀ z, frameDomain (shrinkingContourRadius f hf b hb n) z →
      f.domain (Centered.translate (displacedLocalCenter f hf b hb n) z) := by
  intro z hz
  have hs := rationalFrame_distance b (shrinkingContourRadius f hf b hb n) n z hz
  have hr := Rat.mul_le_mul_of_nonneg_left (half_power_le_one n)
    (Rat.le_of_lt (contourBaseRadius f hf b hb).property)
  have he := divideRadius_identity (hf.openDomain.radius b hb) (⟨4,by decide +kernel⟩ : QPos)
  have hp := (contourBaseRadius f hf b hb).property
  change 4*(contourBaseRadius f hf b hb).val=(hf.openDomain.radius b hb).val at he
  apply hf.openDomain.inside b hb _ (hs.mono _)
  change 3*((contourBaseRadius f hf b hb).val*((1:Rat)/2)^n)≤_
  grind only

def displacedContourErrorStage (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (delta : QPos) : Nat :=
  RationalMajorant.natRateStage (3*(contourBaseRadius f hf b hb).val) delta

theorem displacedContourErrorStage_spec (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (delta : QPos) (n : Nat)
    (hn : displacedContourErrorStage f hf b hb delta≤n) :
    3*(shrinkingContourRadius f hf b hb n).val≤delta.val := by
  have h := contour_half_rate (3*(contourBaseRadius f hf b hb).val)
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (contourBaseRadius f hf b hb).property)) delta n hn
  change 3*((contourBaseRadius f hf b hb).val*((1:Rat)/2)^n)≤delta.val
  grind only

theorem displacedLocalFrame_numerator_close (f : DomainFunctions.Map) (hf : Holomorphic f)
    (b : Scalar) (hb : f.domain b) (eps : QPos) (n : Nat)
    (hn : displacedContourErrorStage f hf b hb (hf.continuous.delta b hb eps)≤n) :
    ∀ z hz, Small (sub (f.eval (Centered.translate (displacedLocalCenter f hf b hb n) z)
      (displacedLocalFrame_domain f hf b hb n z hz)).val (f.eval b hb).val) eps.val := by
  intro z hz
  exact hf.continuous.estimate b hb eps _ _
    ((rationalFrame_distance b (shrinkingContourRadius f hf b hb n) n z hz).mono
      (displacedContourErrorStage_spec f hf b hb _ n hn))

end ComputableAnalysis.RiemannHilbert.RectangularContour
