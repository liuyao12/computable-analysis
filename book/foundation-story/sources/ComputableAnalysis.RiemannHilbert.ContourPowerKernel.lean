import ComputableAnalysis.RiemannHilbert.ContourEffectiveReciprocalBounds

/-! Actual arbitrary-order reciprocal kernels on the punctured numerator
domain. Holomorphy is obtained by iterating the proved product rule. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def ribbonCauchyPowerValue (f : DomainFunctions.Map) (b z : Scalar)
    (hz : (ribbonCauchyKernel f b).domain z) : Nat → Scalar
  | 0 => f.eval z hz.1
  | n+1 => scalarProduct (ribbonCauchyPowerValue f b z hz n) ((ribbonPoleReciprocal b).eval z hz.2)

theorem ribbonCauchyPowerValue_congr (f : DomainFunctions.Map) (b z w : Scalar)
    (hz : (ribbonCauchyKernel f b).domain z) (hw : (ribbonCauchyKernel f b).domain w)
    (he : z≈w) (n : Nat) : ribbonCauchyPowerValue f b z hz n≈ribbonCauchyPowerValue f b w hw n := by
  induction n with
  | zero => exact f.eval_congr z w hz.1 hw.1 he
  | succ n ih =>
    exact mul_equiv (ribbonCauchyPowerValue f b z hz n).property
      (ribbonCauchyPowerValue f b w hw n).property
      ((ribbonPoleReciprocal b).eval z hz.2).property ((ribbonPoleReciprocal b).eval w hw.2).property
      ih ((ribbonPoleReciprocal b).eval_congr z w hz.2 hw.2 he)

def ribbonCauchyPowerKernel (f : DomainFunctions.Map) (b : Scalar) (n : Nat) : DomainFunctions.Map where
  domain := (ribbonCauchyKernel f b).domain
  eval z hz := ribbonCauchyPowerValue f b z hz n
  domain_congr := (ribbonCauchyKernel f b).domain_congr
  eval_congr z w hz hw he := ribbonCauchyPowerValue_congr f b z w hz hw he n

def ribbonCauchyPowerKernel_holomorphic (f : DomainFunctions.Map) (hf : Holomorphic f) (b : Scalar) :
    (n : Nat) → Holomorphic (ribbonCauchyPowerKernel f b n)
  | 0 => hf.onDomain (intersectionOpenData hf (ribbonPoleReciprocal_holomorphic b)) (fun _ hz => hz.1)
  | n+1 => (ribbonCauchyPowerKernel_holomorphic f hf b n).productOn (ribbonPoleReciprocal_holomorphic b)
      (fun _ hz => hz.2)

theorem ribbonCauchyPowerKernel_one (f : DomainFunctions.Map) (b z : Scalar)
    (hz : (ribbonCauchyKernel f b).domain z) :
    (ribbonCauchyPowerKernel f b 1).eval z hz≈(ribbonCauchyKernel f b).eval z hz :=
  equiv_refl _ ((ribbonCauchyKernel f b).eval z hz).property

theorem ribbonCauchyPowerKernel_two (f : DomainFunctions.Map) (b z : Scalar)
    (hz : (ribbonCauchyKernel f b).domain z) :
    (ribbonCauchyPowerKernel f b 2).eval z hz≈(ribbonCauchyDerivativeKernel f b).eval z hz :=
  equiv_refl _ ((ribbonCauchyDerivativeKernel f b).eval z hz).property

theorem ribbonCauchyPowerKernel_pole_congr (f : DomainFunctions.Map) (b c z : Scalar) (he : b≈c)
    (hb : (ribbonCauchyKernel f b).domain z) (hc : (ribbonCauchyKernel f c).domain z) (n : Nat) :
    (ribbonCauchyPowerKernel f b n).eval z hb≈(ribbonCauchyPowerKernel f c n).eval z hc := by
  induction n with
  | zero => exact equiv_refl _ (f.eval z hb.1).property
  | succ n ih =>
    exact mul_equiv (ribbonCauchyPowerValue f b z hb n).property
      (ribbonCauchyPowerValue f c z hc n).property
      ((ribbonPoleReciprocal b).eval z hb.2).property ((ribbonPoleReciprocal c).eval z hc.2).property
      ih (ribbonPoleReciprocal_congr b c z he hb.2 hc.2)

theorem ribbonPoleReciprocal_derivative_agreement (b z : Scalar) (hz : (ribbonPoleReciprocal b).domain z) :
    (ribbonPoleReciprocal_holomorphic b).derivative z hz≈
      scalarNeg (scalarProduct ((ribbonPoleReciprocal b).eval z hz) ((ribbonPoleReciprocal b).eval z hz)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((ribbonPoleReciprocal_holomorphic b).derivative z hz).property)
    (hright := (scalarNeg (scalarProduct ((ribbonPoleReciprocal b).eval z hz) ((ribbonPoleReciprocal b).eval z hz))).property)
  let R := gridScalarValue ((ribbonPoleReciprocal b).eval z hz)
  change (-(R*R))*1= -(R*R)
  grind only

theorem ribbonPoleReciprocal_derivative_bound (b z : Scalar) (hz : (ribbonPoleReciprocal b).domain z)
    (U : QPos) (hr : Small ((ribbonPoleReciprocal b).eval z hz).val U.val) :
    Small ((ribbonPoleReciprocal_holomorphic b).derivative z hz).val (2*U.val*U.val) :=
  Small.congr (neg_valid (mul_valid ((ribbonPoleReciprocal b).eval z hz).property ((ribbonPoleReciprocal b).eval z hz).property))
    ((ribbonPoleReciprocal_holomorphic b).derivative z hz).property
    (equiv_symm (ribbonPoleReciprocal_derivative_agreement b z hz))
    (SeriesLimitLaws.small_neg (Small.mul ((ribbonPoleReciprocal b).eval z hz).property ((ribbonPoleReciprocal b).eval z hz).property (Rat.le_of_lt U.property) (Rat.le_of_lt U.property) hr hr))

end ComputableAnalysis.RiemannHilbert.RectangularContour
