import ComputableAnalysis.RiemannHilbert.ContourPowerKernel

/-! Executable value and derivative bounds for arbitrary reciprocal powers.
Only the numerator's actual first derivative is used; higher derivatives or
Taylor coefficients are not supplied as hypotheses. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def powerKernelValueBound (F U : QPos) : Nat → QPos
  | 0 => F
  | n+1 => ⟨2*(powerKernelValueBound F U n).val*U.val,
      Rat.mul_pos (Rat.mul_pos (by decide +kernel) (powerKernelValueBound F U n).property) U.property⟩

def powerKernelDerivativeBound (F D U : QPos) : Nat → QPos
  | 0 => D
  | n+1 => ⟨2*(powerKernelDerivativeBound F D U n).val*U.val+
      4*(powerKernelValueBound F U n).val*U.val*U.val,
      by
        have h1 := Rat.mul_pos (Rat.mul_pos (show (0:Rat)<2 by decide +kernel) (powerKernelDerivativeBound F D U n).property) U.property
        have h2 := Rat.mul_pos (Rat.mul_pos (Rat.mul_pos (show (0:Rat)<4 by decide +kernel) (powerKernelValueBound F U n).property) U.property) U.property
        grind only⟩

theorem ribbonCauchyPowerKernel_value_bound (f : DomainFunctions.Map) (b z : Scalar)
    (hz : (ribbonCauchyKernel f b).domain z) (F U : QPos)
    (hF : Small (f.eval z hz.1).val F.val) (hU : Small ((ribbonPoleReciprocal b).eval z hz.2).val U.val)
    (n : Nat) : Small ((ribbonCauchyPowerKernel f b n).eval z hz).val (powerKernelValueBound F U n).val := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    exact Small.mul (ribbonCauchyPowerValue f b z hz n).property ((ribbonPoleReciprocal b).eval z hz.2).property
      (Rat.le_of_lt (powerKernelValueBound F U n).property) (Rat.le_of_lt U.property) ih hU

theorem ribbonCauchyPowerKernel_derivative_bound (f : DomainFunctions.Map) (hf : Holomorphic f) (b z : Scalar)
    (hz : (ribbonCauchyKernel f b).domain z) (F D U : QPos)
    (hF : Small (f.eval z hz.1).val F.val) (hD : Small (hf.derivative z hz.1).val D.val)
    (hU : Small ((ribbonPoleReciprocal b).eval z hz.2).val U.val) (n : Nat) :
    Small ((ribbonCauchyPowerKernel_holomorphic f hf b n).derivative z hz).val (powerKernelDerivativeBound F D U n).val := by
  induction n with
  | zero => exact hD
  | succ n ih =>
    have hv := ribbonCauchyPowerKernel_value_bound f b z hz F U hF hU n
    have hr := ribbonPoleReciprocal_derivative_bound b z hz.2 U hU
    have hl := Small.mul ((ribbonCauchyPowerKernel_holomorphic f hf b n).derivative z hz).property
      ((ribbonPoleReciprocal b).eval z hz.2).property
      (Rat.le_of_lt (powerKernelDerivativeBound F D U n).property) (Rat.le_of_lt U.property) ih hU
    have hright := Small.mul ((ribbonCauchyPowerKernel f b n).eval z hz).property
      ((ribbonPoleReciprocal_holomorphic b).derivative z hz.2).property
      (Rat.le_of_lt (powerKernelValueBound F U n).property)
      (Rat.le_of_lt (Rat.mul_pos (Rat.mul_pos (by decide +kernel) U.property) U.property)) hv hr
    have hs := LocalODE.small_add hl hright
    have he : 2*(powerKernelDerivativeBound F D U n).val*U.val+
        2*(powerKernelValueBound F U n).val*(2*U.val*U.val)=
        (powerKernelDerivativeBound F D U (n+1)).val := by
      dsimp [powerKernelDerivativeBound]; grind only
    rw [he] at hs
    exact hs

theorem ribbonCauchyPowerBoundaryDomains (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hdom : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (n : Nat) : RectangleBoundaryDomains (ribbonCauchyPowerKernel f b n) J :=
  let hd := rectangleCauchyBoundaryDomains f J hdom b hb
  ⟨hd.bottom,hd.top,hd.left,hd.right⟩

theorem ribbonCauchyPowerBoundary_derivative_bound (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hdom : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b)
    (hdf : RectangleBoundaryDomains f J) (hdR : RectangleBoundaryDomains (ribbonPoleReciprocal b) J)
    (F D U : QPos) (hF : RectangleBoundaryValueBound f J hdf F)
    (hD : RectangleBoundaryDerivativeBound f hf J hdf D)
    (hU : RectangleBoundaryValueBound (ribbonPoleReciprocal b) J hdR U) (n : Nat) :
    RectangleBoundaryDerivativeBound (ribbonCauchyPowerKernel f b n) (ribbonCauchyPowerKernel_holomorphic f hf b n)
      J (ribbonCauchyPowerBoundaryDomains f J hdom b hb n) (powerKernelDerivativeBound F D U n) where
  bottom := fun z hz => ribbonCauchyPowerKernel_derivative_bound f hf b z _ F D U
    (hF.bottom z hz) (hD.bottom z hz) (hU.bottom z hz) n
  top := fun z hz => ribbonCauchyPowerKernel_derivative_bound f hf b z _ F D U
    (hF.top z hz) (hD.top z hz) (hU.top z hz) n
  left := fun z hz => ribbonCauchyPowerKernel_derivative_bound f hf b z _ F D U
    (hF.left z hz) (hD.left z hz) (hU.left z hz) n
  right := fun z hz => ribbonCauchyPowerKernel_derivative_bound f hf b z _ F D U
    (hF.right z hz) (hD.right z hz) (hU.right z hz) n

end ComputableAnalysis.RiemannHilbert.RectangularContour
